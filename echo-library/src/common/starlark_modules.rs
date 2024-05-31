use super::*;
use anyhow::anyhow;

fn validate_value(value: &serde_json::Value, expected_type: &RustType) -> anyhow::Result<()> {
    match expected_type {
        RustType::String => {
            if !value.is_string() {
                return Err(anyhow!("Value must be a string"));
            }
        }
        RustType::Int => {
            if !value.is_i64() {
                return Err(anyhow!("Value must be an integer"));
            }
        }
        RustType::Float => {
            if !value.is_f64() {
                return Err(anyhow!("Value must be a float"));
            }
        }
        RustType::Uint => {
            if !value.is_u64() {
                return Err(anyhow!("Value must be a positive integer"));
            }
        }
        RustType::Boolean => {
            if !value.is_boolean() {
                return Err(anyhow!("Value must be a boolean"));
            }
        }

        RustType::Struct(_) => {}

        RustType::Value => {
            if !value.is_object() {
                return Err(anyhow!("value must be a Json Object"));
            }
        }

        RustType::HashMap(key_type, value_type) => {
            if let Some(map) = value.as_object() {
                for (key, val) in map.iter() {
                    validate_value(val, value_type)?;
                }
            } else {
                return Err(anyhow!("Value must be a JSON object"));
            }
        }

        RustType::List(item_type) => {
            let parsed_array = value
                .as_array()
                .ok_or_else(|| anyhow!("Value must be a JSON array"))?;

            for element in parsed_array.iter() {
                validate_value(element, item_type)?;
            }
        }

        RustType::Tuple(key_type, value_type) => {
            let parsed_tuple = value
                .as_array()
                .ok_or_else(|| anyhow!("Value must be a JSON tuple with two elements"))?;

            if parsed_tuple.len() != 2 {
                return Err(anyhow!("Tuple must have exactly two elements"));
            }

            // Pattern matching for key and value types
            match (&parsed_tuple[0], &parsed_tuple[1]) {
                (serde_json::Value::String(key), value) => validate_value(value, value_type)?,
                (serde_json::Value::Number(number), value) if number.is_i64() => {
                    validate_value(value, value_type)?
                }
                (serde_json::Value::Number(number), value) if number.is_f64() => {
                    validate_value(value, value_type)?
                }
                (serde_json::Value::Bool(bool_value), value) => validate_value(value, value_type)?,
                _ => return Err(anyhow!("Unsupported tuple element types")),
            }
        }

        _ => return Err(anyhow!("Unsupported input type for default value")),
    }

    Ok(())
}

#[allow(clippy::type_complexity)]
#[starlark_module]
pub fn starlark_workflow_module(builder: &mut GlobalsBuilder) {
    /// Creates a new task of the workflow and returns a task object of `Task` type
    /// This method will be invoked inside the config file.
    ///
    /// # Arguments
    ///
    /// * `kind` - A string that holds the kind of the task (i.e "polkadot", "openwhisk")
    /// * `action_name` - A string that holds the the name of the action associated with the task
    /// * `input_args` - The input arguments for the task
    /// * `attributes` - The attributes of the task
    /// * `operation` - An optional argument to mention type of the task operation
    /// * `depend_on` - The dependencies of the task
    ///   (i.e "map", "concat")
    ///
    /// # Returns
    ///
    /// * A Result containing the task object if the task is created successfully
    ///
    fn task(
        kind: String,
        action_name: String,
        input_arguments: Value,
        attributes: Option<Value>,
        operation: Option<Value>,
        depend_on: Option<Value>,
    ) -> anyhow::Result<Task> {
        if kind == "openwhisk" || kind == "polkadot" {
            if attributes.is_none() {
                return Err(anyhow!(
                    "Attributes are mandatory for kind: openwhisk or polkadot"
                ));
            }
        }

        let mut input_arguments: Vec<Input> = serde_json::from_str(&input_arguments.to_json()?)
            .map_err(|err| anyhow!("Failed to parse input arguments: {}", err))?;

        let attributes: HashMap<String, String> = match attributes {
            Some(attributes) => serde_json::from_str(&attributes.to_json()?)
                .map_err(|err| anyhow!("Failed to parse the attributes: {}", err))?,
            _ => HashMap::default(),
        };

        let depend_on: Vec<Depend> = match depend_on {
            Some(val) => serde_json::from_str(&val.to_json()?)
                .map_err(|err| anyhow!("Failed to parse depend-on: {}", err))?,
            None => Vec::default(),
        };

        for depend in depend_on.iter() {
            for argument in input_arguments.iter_mut() {
                if argument.name == depend.cur_field {
                    argument.is_depend = true;
                    break;
                }
            }
        }

        let operation: Operation = match operation {
            Some(op) => serde_json::from_str(&op.to_json()?)
                .map_err(|err| anyhow!("Failed to parse the task operation value: {}", err))?,
            _ => Operation::Normal,
        };

        Ok(Task {
            kind,
            action_name,
            input_arguments,
            attributes,
            operation,
            depend_on,
        })
    }

    /// Creates and adds a new workflow to the composer
    /// This method will be invoked inside the config file.
    ///
    /// # Arguments
    ///
    /// * `name` - A string that holds the name of the workflow
    /// * `version` - A string that holds the version of the workflow
    /// * `tasks` - The tasks of the workflow
    /// * `custom_types` - Optional custom types for the workflow
    /// * `eval` - A mutable reference to the Evaluator (injected by the starlark rust package)
    ///
    /// # Returns
    ///
    /// * a workflow object of `Workflow` type
    ///
    fn workflows(
        name: String,
        version: String,
        tasks: Value,
        eval: &mut Evaluator,
    ) -> anyhow::Result<Workflow> {
        let tasks: Vec<Task> = serde_json::from_str(&tasks.to_json()?)
            .map_err(|err| anyhow!("Failed to parse task value: {}", err))?;

        let mut task_hashmap = HashMap::new();

        for task in tasks {
            if task_hashmap.contains_key(&task.action_name) {
                return Err(Error::msg("Duplicate tasks, Task names must be unique"));
            } else {
                task_hashmap.insert(task.action_name.clone(), task);
            }
        }

        eval.extra
            .as_ref()
            .and_then(|extra| extra.downcast_ref::<Composer>())
            .ok_or_else(|| anyhow!("Failed to obtain Composer from Evaluator"))?
            .add_workflow(name.clone(), version.clone(), task_hashmap.clone())
            .map_err(|err| anyhow!("Failed to add workflow: {}", err))?;

        Ok(Workflow {
            name,
            version,
            tasks: task_hashmap,
        })
    }

    /// Creates a new field for the input argument of a task
    ///
    /// # Arguments
    ///
    /// * `name` - A string that holds the name of the input field
    /// * `input_type` - A string that holds the type of the input field
    /// * `default_value` - An optional JSON default value for the input field
    ///
    /// # Returns
    ///
    /// * A Result containing the input object of `Input` type
    ///

    fn argument(
        name: String,
        input_type: Value,
        default_value: Option<Value>,
    ) -> anyhow::Result<Input> {
        let input_type: RustType = serde_json::from_str(&input_type.to_json()?)
            .map_err(|err| anyhow!("Failed to parse input arguments: {}", err))?;

        let default_value: Option<String> = match default_value {
            Some(value) => {
                let value_str = value
                    .to_json()
                    .map_err(|err| anyhow!("Failed to parse default value: {}", err))?;

                let parsed_value = serde_json::from_str(&value_str)?;
                validate_value(&parsed_value, &input_type)?;

                Some(value_str)
            }
            None => Default::default(),
        };

        Ok(Input {
            name,
            input_type,
            default_value,
            is_depend: false,
        })
    }

    fn depend(task_name: String, cur_field: String, prev_field: String) -> anyhow::Result<Depend> {
        Ok(Depend {
            task_name,
            cur_field,
            prev_field,
        })
    }

    /// Creates a user-defined type inside the `types.rs`.
    /// This method will be invoked inside the config file.
    ///
    /// # Arguments
    ///
    /// * `name` - The name of the user-defined type
    /// * `fields` - The fields of the user-defined type in JSON format
    /// * `eval` - A mutable reference to the Evaluator (injected by the starlark rust package)
    ///
    /// # Returns
    ///
    /// * A Result containing the name of the user-defined type
    ///
    fn EchoStruct(name: String, fields: Value, eval: &mut Evaluator) -> anyhow::Result<RustType> {
        let fields: HashMap<String, RustType> = serde_json::from_str(&fields.to_json()?)
            .map_err(|err| anyhow!("Failed to parse fields: {}", err))?;

        let composer = eval
            .extra
            .as_ref()
            .and_then(|extra| extra.downcast_ref::<Composer>())
            .ok_or_else(|| anyhow!("Failed to obtain Composer from Evaluator"))?;
        let name = name.to_case(Case::Pascal);

        let mut build_string = Vec::new();

        for (key, value) in fields {
            build_string.push(format!("{}:{}", key, value));
        }

        let build_string = format!("[{}]", build_string.join(","));

        composer
            .custom_types
            .borrow_mut()
            .insert(
                name.to_string(),
                format!(
                "make_input_struct!(\n{},\n{},\n[Default, Clone, Debug, Deserialize, Serialize]\n);",
                &name,
                build_string
            ));

        Ok(RustType::Struct(name))
    }
}

#[starlark_module]
pub fn starlark_datatype_module(builder: &mut GlobalsBuilder) {
    /// Returns the Rust type for a tuple with specified types of the key and vale
    /// This method will be invoked inside the config file.
    ///
    /// # Arguments
    ///
    /// * `type_1` - The type of the tuple field-1
    /// * `type_2` - The type of the tuple field-2
    ///
    /// # Returns
    ///
    /// * A Result containing the Rust type for a map
    ///
    fn Tuple(type_1: Value, type_2: Value) -> anyhow::Result<RustType> {
        let type_1: RustType = serde_json::from_str(&type_1.to_json()?)
            .map_err(|err| anyhow!("Failed to parse values: {}", err))?;
        let type_2: RustType = serde_json::from_str(&type_2.to_json()?)
            .map_err(|err| anyhow!("Failed to parse values: {}", err))?;

        Ok(RustType::Tuple(Box::new(type_1), Box::new(type_2)))
    }

    /// Returns the Rust type for a map with specified types of the key and vale
    /// This method will be invoked inside the config file.
    ///
    /// # Arguments
    ///
    /// * `type_1` - The type of the key
    /// * `type_2` - The type of the value
    ///
    /// # Returns
    ///
    /// * A Result containing the Rust type for a map
    ///
    fn HashMap(type_1: Value, type_2: Value) -> anyhow::Result<RustType> {
        let type_1: RustType = serde_json::from_str(&type_1.to_json()?)
            .map_err(|err| anyhow!("Failed to parse values: {}", err))?;
        let type_2: RustType = serde_json::from_str(&type_2.to_json()?)
            .map_err(|err| anyhow!("Failed to parse values: {}", err))?;

        Ok(RustType::HashMap(Box::new(type_1), Box::new(type_2)))
    }

    /// Returns the Rust type for a list with specified element type
    /// This method will be invoked inside the config file.
    ///
    /// # Arguments
    ///
    /// * `type_of` - The type of the element in the list
    ///
    /// # Returns
    ///
    ///  * A Result containing the Rust type for a list
    ///
    fn List(type_of: Value) -> anyhow::Result<RustType> {
        let type_of: RustType = serde_json::from_str(&type_of.to_json()?)
            .map_err(|err| anyhow!("Failed to parse values: {}", err))?;
        Ok(RustType::List(Box::new(type_of)))
    }
}

#[starlark_module]
pub fn starlark_operation_module(builder: &mut GlobalsBuilder) {
    /// Returns `Operation::Normal` task-operation type to the config file
    /// This method will be invoked inside the config file
    ///
    /// # Returns
    ///
    /// * A Result containing Operation::Normal
    ///   
    fn normal() -> anyhow::Result<Operation> {
        Ok(Operation::Normal)
    }

    /// Returns `Operation::Concat` task-operation type to the config file
    /// This method will be invoked inside the config file
    ///
    /// # Returns
    ///
    /// * A Result containing Operation::Concat
    ///   
    fn concat() -> anyhow::Result<Operation> {
        Ok(Operation::Concat)
    }

    /// Returns `Operation::Concat` task-operation type to the config file
    /// This method will be invoked inside the config file
    ///
    /// # Returns
    ///
    /// * A Result containing Operation::Concat
    ///   
    fn combine() -> anyhow::Result<Operation> {
        Ok(Operation::Combine)
    }

    /// Returns `Operation::Map(field)` task-operation type to the config file
    /// This method will be invoked inside the config file
    ///
    /// # Arguments
    ///
    /// * `field` - A String containing name of the field that should be fetch from the previous task
    ///
    /// # Returns
    ///
    /// * A Result containing Operation::Map(field)
    ///   
    fn map(field: String) -> anyhow::Result<Operation> {
        Ok(Operation::Map(field))
    }
}
