#![warn(clippy::todo)]

use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt::Debug,
    fs,
    hash::Hash,
    io::{BufWriter, Write},
    process::exit,
};

use clap::Parser as ClapParser;
use dyn_clone::DynClone;
use pest::{iterators::Pair, Parser};
use pest_derive::Parser;
use rand::distributions::{Alphanumeric, DistString};

#[derive(Debug, ClapParser)]
struct Args {
    /// The output file, defaults to <FILE>.s
    #[arg(short)]
    output: Option<String>,

    /// The SimpleC file to compile
    file: String,
}

#[derive(Debug, Parser)]
#[grammar = "simplec.pest"]
struct SimpleCParser;

/// Any place you can store to and retrieve from
/// Examples include Registers, the Stack, and RAM
trait Memory: ToString + Debug + DynClone {
    // Decides whether a dereference is necessary
    fn is_register(&self) -> bool;

    /// For address of operator
    /// Panics if a register
    fn stack_offset(&self) -> usize {
        panic!("This is not a stack! Stack offset not implemented.")
    }
}

dyn_clone::clone_trait_object!(Memory);

#[derive(Debug, Clone, Copy)]
enum CalleeSavedRegister {
    Rbx,
    R10,
    R13,
    R14,
    R15,
}

const REGISTER_STACK: [CalleeSavedRegister; 5] = [
    CalleeSavedRegister::Rbx,
    CalleeSavedRegister::R10,
    CalleeSavedRegister::R13,
    CalleeSavedRegister::R14,
    CalleeSavedRegister::R15,
];

impl Memory for CalleeSavedRegister {
    fn is_register(&self) -> bool {
        true
    }
}

impl ToString for CalleeSavedRegister {
    fn to_string(&self) -> String {
        match self {
            CalleeSavedRegister::Rbx => "%rbx",
            CalleeSavedRegister::R10 => "%r10",
            CalleeSavedRegister::R13 => "%r13",
            CalleeSavedRegister::R14 => "%r14",
            CalleeSavedRegister::R15 => "%r15",
        }
        .to_string()
    }
}

#[derive(Debug, Clone, Copy)]
struct StackAllocation {
    offset: usize,
}

impl ToString for StackAllocation {
    fn to_string(&self) -> String {
        format!("-{}(%rbp)", self.offset)
    }
}

impl Memory for StackAllocation {
    fn is_register(&self) -> bool {
        false
    }

    fn stack_offset(&self) -> usize {
        self.offset
    }
}

#[derive(Debug, Clone, Copy)]
enum ArgumentRegister {
    Rdi,
    Rsi,
    Rdx,
    Rcx,
    R8,
    R9,
}

const ARGUMENT_REGISTERS: [ArgumentRegister; 6] = [
    ArgumentRegister::Rdi,
    ArgumentRegister::Rsi,
    ArgumentRegister::Rdx,
    ArgumentRegister::Rcx,
    ArgumentRegister::R8,
    ArgumentRegister::R9,
];

impl Memory for ArgumentRegister {
    fn is_register(&self) -> bool {
        false
    }
}

impl ToString for ArgumentRegister {
    fn to_string(&self) -> String {
        match self {
            ArgumentRegister::Rdi => "%rdi",
            ArgumentRegister::Rsi => "%rsi",
            ArgumentRegister::Rdx => "%rdx",
            ArgumentRegister::Rcx => "%rcx",
            ArgumentRegister::R8 => "%r8",
            ArgumentRegister::R9 => "%r9",
        }
        .to_string()
    }
}

#[derive(Debug, Clone, Copy)]
enum UtilRegister {
    Rax,
    Rbp,
}

impl Memory for UtilRegister {
    fn is_register(&self) -> bool {
        true
    }
}

impl ToString for UtilRegister {
    fn to_string(&self) -> String {
        match self {
            Self::Rax => "%rax",
            Self::Rbp => "%rbp",
        }
        .to_string()
    }
}

#[derive(Debug)]
enum ProgramItem {
    /// Generates a global with a name
    /// Type is not necessary since types don't really exist
    Global(String),
    Function {
        name: String,
        stack_allocs: usize,
        arg_destinations: Vec<Box<dyn Memory>>,
        children: Vec<ProgramItem>,
    },
    FunctionCall {
        name: String,
        args: Vec<Box<dyn Memory>>,
    },
    Expression {
        stack: Vec<ExpressionInstruction>,
        /// Where the output of the expression will be found once the stack is executed
        output: Box<dyn Memory>,
        destination: ExpressionDestination,
    },
    Return {
        name: String,
        value: Vec<ProgramItem>,
    },
}

impl ProgramItem {
    fn write<W: Write>(self, writer: &mut W) -> Result<(), std::io::Error> {
        match self {
            ProgramItem::Global(name) => {
                writer.write_all(format!(".data\n\t.comm {name}, 8\n").as_bytes())
            }
            ProgramItem::Function {
                name,
                stack_allocs,
                arg_destinations,
                children,
            } => {
                // Header
                writer.write_all(format!(".text\n.globl {name}\n{name}:\n").as_bytes())?;

                // Frame pointer
                writer.write_all(b"\tpushq %rbp\n\tmovq %rsp, %rbp\n")?;

                // Registers
                let mut callee_saved = vec![
                    CalleeSavedRegister::Rbx,
                    CalleeSavedRegister::Rbx,
                    CalleeSavedRegister::R10,
                    CalleeSavedRegister::R13,
                    CalleeSavedRegister::R14,
                    CalleeSavedRegister::R15,
                ];

                for register in &callee_saved {
                    writer.write_all(format!("\tpushq {}\n", register.to_string()).as_bytes())?;
                }

                // Make sure stack is aligned to 16 bytes
                let stack_allocs = if stack_allocs % 2 == 0 {
                    stack_allocs
                } else {
                    stack_allocs + 1
                } - 6;

                if stack_allocs > 0 {
                    writer.write_all(format!("\tsubq ${}, %rsp\n", stack_allocs * 8).as_bytes())?;
                }

                // Args
                for (arg_dest, reg) in arg_destinations.into_iter().zip(ARGUMENT_REGISTERS) {
                    writer.write_all(
                        format!("\tmovq {}, {}\n", reg.to_string(), arg_dest.to_string())
                            .as_bytes(),
                    )?;
                }

                // Content
                for child in children {
                    child.write(writer)?;
                }

                // Add a label for a RETURN jump
                writer.write_all(format!("__{name}_exit:\n").as_bytes())?;

                if stack_allocs > 0 {
                    writer.write_all(format!("\taddq ${}, %rsp\n", stack_allocs * 8).as_bytes())?;
                }

                // Restore registers
                callee_saved.reverse();
                for register in &callee_saved {
                    writer.write_all(format!("\tpopq {}\n", register.to_string()).as_bytes())?;
                }

                // Leave and return
                writer.write_all(b"\tleave\n\tret\n")?;

                Ok(())
            }
            Self::FunctionCall { name, args } => {
                assert!(
                    args.len() <= ARGUMENT_REGISTERS.len(),
                    "More args than supported for function `{name}`"
                );

                for (src, reg) in args.into_iter().zip(ARGUMENT_REGISTERS) {
                    // writer.write_all(format!("\tmovq %{} %{}\n", src.to_string(), dest.to_string()).as_bytes())?;
                    writer.write_all(
                        format!("\tmovq {}, {}\n", src.to_string(), reg.to_string()).as_bytes(),
                    )?;
                }

                // Safety for variadics if called
                writer.write_all(b"\txorq %rax, %rax\n")?;

                writer.write_all(format!("\tcall {name}\n").as_bytes())?;

                Ok(())
            }
            Self::Expression {
                stack,
                output,
                destination,
            } => {
                for instruction in stack {
                    instruction.write(writer)?;
                }

                match destination {
                    ExpressionDestination::Variable(v) => match v {
                        RealizedVariable::Memory(m) => {
                            if !output.is_register() && !m.is_register() {
                                writer.write_all(
                                    format!("\tmovq {}, %r15\n", output.to_string()).as_bytes(),
                                )?;
                                writer.write_all(
                                    format!("\tmovq %r15, {}\n", m.to_string()).as_bytes(),
                                )?;
                            } else {
                                writer.write_all(
                                    format!("\tmovq {}, {}\n", output.to_string(), m.to_string())
                                        .as_bytes(),
                                )?;
                            }
                        }
                        RealizedVariable::Global(g) => {
                            let (output, flag): (Box<dyn Memory>, bool) = if !output.is_register() {
                                writer.write_all(
                                    format!("\tpushq %r14\n\tmovq {}, %r14\n", output.to_string())
                                        .as_bytes(),
                                )?;
                                (Box::new(CalleeSavedRegister::R14), true)
                            } else {
                                (output, false)
                            };

                            writer.write_all(
                                format!(
                                    "\tmovq ${g}, %r15\n\tmovq {}, (%r15)\n",
                                    output.to_string()
                                )
                                .as_bytes(),
                            )?;

                            if flag {
                                writer.write_all(b"\tpopq %r14\n")?;
                            }
                        },
                        RealizedVariable::Offset { base, offsets, items } => {
                            for item in items {
                                item.write(writer)?;
                            }

                            writer.write_all(
                                format!("\tpushq %r14\n\tmovq {}, %r14\n", output.to_string())
                                    .as_bytes(),
                            )?;

                            match *base {
                                RealizedVariable::Memory(mem) => {
                                    writer.write_all(b"\tmovq %rbp, %r15\n")?;
                                    writer.write_all(format!("\tsubq ${}, %r15\n", mem.stack_offset()).as_bytes())?;
                                },
                                RealizedVariable::Global(name) => {
                                    writer.write_all(format!("\tmovq ${name}, %r15\n").as_bytes())?;
                                },
                                RealizedVariable::Offset{..} => unreachable!(),
                            }

                            writer.write_all(b"\tmovq (%r15), %r15\n")?;

                            for offset in offsets.iter().take(offsets.len() - 1) {
                                writer.write_all(format!("\taddq {}, %r15\n", offset.to_string()).as_bytes())?;
                                writer.write_all(b"\tmovq (%r15), %r15\n")?;
                            }

                            writer.write_all(format!("\taddq {}, %r15\n", offsets.last().unwrap().to_string()).as_bytes())?;
                            writer.write_all(b"\tmovq %r14, (%r15)\n\tpopq %r14\n")?;
                        },
                    },
                    ExpressionDestination::ConditionalJump(_) => todo!(),
                }

                Ok(())
            }
            Self::Return { name, value } => {
                if value.is_empty() {
                    // Return 0
                    writer.write_all(b"\txorq %rax, %rax\n")?;
                } else {
                    for value in value {
                        value.write(writer)?;
                    }
                }

                writer.write_all(format!("\tjmp __{}_exit\n", name).as_bytes())?;

                Ok(())
            }
        }
    }
}

fn main() {
    let args = Args::parse();

    let file = fs::read_to_string(&args.file);

    let file = match file {
        Ok(contents) => contents,
        Err(e) => {
            eprintln!("Failed to open file: {e}");
            exit(2);
        }
    };

    let file = &file;

    let parsed = SimpleCParser::parse(Rule::program, file);

    let parsed = match parsed {
        Ok(pairs) => pairs,
        Err(e) => {
            eprintln!("Failed to parse file! {e}");
            exit(3);
        }
    };

    let program = parsed.into_iter().next().unwrap();

    let c_file_with_assembly_suffix = {
        let mut file = args
            .file
            .split('.')
            .map(|s| s.to_owned())
            .collect::<Vec<_>>();
        let _ = file.pop();
        file.push("s".to_string());
        file.join(".")
    };

    let file = fs::File::create(args.output.unwrap_or(c_file_with_assembly_suffix));

    let file = match file {
        Ok(f) => f,
        Err(e) => {
            eprintln!("Failed to open file! {e}");
            exit(4);
        }
    };

    let mut writer = BufWriter::new(file);

    let mut globals = HashSet::new();

    // All of the strings generated by the program
    let mut strings: Vec<String> = Vec::new();

    program
        .into_inner()
        .flat_map(|pair| match pair.as_rule() {
            Rule::function => vec![handle_function(pair, &globals, &mut strings)],
            Rule::decl => handle_global_decl(pair, &mut globals),
            _ => unreachable!(),
        })
        .for_each(|pi: ProgramItem| pi.write(&mut writer).unwrap());

    for (i, value) in strings.iter().enumerate() {
        writer
            .write_all(format!(".data\nglobal_string_{i}:\n\t.string {value}\n").as_bytes())
            .unwrap();
    }

    writer.flush().unwrap();
}

/// Handle potentially multiple globals
fn handle_global_decl(pair: Pair<'_, Rule>, globals: &mut HashSet<String>) -> Vec<ProgramItem> {
    let mut pairs = pair.into_inner();
    let _ty = pairs.next().unwrap().into_inner();

    // let num_indirection = ty
    //     .filter(|pair| matches!(pair.as_rule(), Rule::pointer))
    //     .count();

    let decl_ident_list = pairs.next().unwrap();

    decl_ident_list
        .into_inner()
        .map(|ident| {
            let ident = ident.as_str().to_string();

            if globals.iter().any(|g| g == ident.as_str()) {
                panic!(
                    "Variable redeclaration error! Variable `{}` is defined more than once.",
                    ident.as_str()
                );
            }

            globals.insert(ident.clone());

            ProgramItem::Global(ident)
        })
        .collect()
}

#[derive(Debug, Clone, Copy)]
struct MemoryManager {
    register_allocs: usize,
    stack_allocs: usize,
}

impl Default for MemoryManager {
    fn default() -> Self {
        Self {
            register_allocs: 0,
            stack_allocs: 6,
        }
    }
}

impl MemoryManager {
    fn next_free_memory(&mut self) -> Box<dyn Memory> {
        if self.register_allocs < 4 {
            self.register_allocs += 1;
            Box::new(REGISTER_STACK[self.register_allocs - 1])
        } else {
            self.next_free_stack_memory()
        }
    }

    fn next_free_stack_memory(&mut self) -> Box<dyn Memory> {
        self.stack_allocs += 1;
        Box::new(StackAllocation {
            offset: 8 * (self.stack_allocs - 1),
        })
    }
}

#[derive(Debug)]
enum RealizedVariable {
    Memory(Box<dyn Memory>),
    Offset {
        /// The base identifier, either a Memory location or a Global
        base: Box<RealizedVariable>,
        /// The offsets that must be used to get to the final memory location
        offsets: Vec<Box<dyn Memory>>,
        /// Program items that must be executed in order to fill the `offsets`
        items: Vec<ProgramItem>,
    },
    Global(String),
}

fn handle_function(
    pair: Pair<'_, Rule>,
    globals: &HashSet<String>,
    strings: &mut Vec<String>,
) -> ProgramItem {
    let mut pairs = pair.into_inner();
    let ident = pairs.nth(1).unwrap().as_str();

    let arg_list = pairs.next();

    let has_args_list = arg_list.clone().is_some_and(|pair| {
        pair.into_inner()
            .any(|p| matches!(p.as_rule(), Rule::function_arg))
    });
    let args_list_is_statements = arg_list.is_some() && !has_args_list;

    let arg_list_str = if has_args_list {
        arg_list
            .clone()
            .unwrap()
            .into_inner()
            .map(|arg| {
                let arg = arg.into_inner();
                for arg_part in arg {
                    if matches!(arg_part.as_rule(), Rule::ident) {
                        return arg_part.as_str().to_string();
                    }
                }
                unreachable!();
            })
            .collect()
    } else {
        Vec::new()
    };

    let statements = if args_list_is_statements {
        arg_list
    } else {
        pairs.next()
    };

    let mut local_stack = HashMap::<String, Box<dyn Memory>>::new();
    let mut memory = MemoryManager::default();

    let mut arg_mems = Vec::new();
    for arg in arg_list_str {
        // Allocate stack memory since &ident may happen
        let mem = memory.next_free_stack_memory();
        local_stack.insert(arg, mem.to_owned());
        arg_mems.push(mem);
    }

    // Function may not have a body
    let children: Vec<ProgramItem> = if let Some(statements) = statements {
        statements
            .into_inner()
            .flat_map(|statement| match statement.as_rule() {
                Rule::decl => {
                    handle_local_decl(statement, &mut memory, &mut local_stack, globals);
                    vec![]
                }
                Rule::assignment => {
                    handle_assignment(statement, &mut memory, &local_stack, globals, strings)
                }
                Rule::call => {
                    handle_function_call(statement, &mut memory, &local_stack, globals, strings)
                }
                Rule::if_expr => todo!(),
                Rule::while_expr => todo!(),
                Rule::do_while_expr => todo!(),
                Rule::for_expr => todo!(),
                Rule::flow_control => {
                    // continue and return are not allowed in the outermost scope, so this has to be a return
                    let flow_control = statement.into_inner().next().unwrap().into_inner().next();

                    vec![ProgramItem::Return {
                        name: ident.to_string(),
                        value: flow_control
                            .map(|p| {
                                handle_expression(
                                    p,
                                    &mut memory,
                                    &local_stack,
                                    globals,
                                    ExpressionDestination::Variable(RealizedVariable::Memory(Box::new(
                                        UtilRegister::Rax,
                                    ))),
                                    strings,
                                )
                            })
                            .unwrap_or_default(),
                    }]
                }
                _ => unreachable!(),
            })
            .collect()
    } else {
        vec![]
    };

    ProgramItem::Function {
        name: ident.to_string(),
        stack_allocs: memory.stack_allocs,
        arg_destinations: arg_mems,
        children,
    }
}

fn handle_function_call(
    pair: Pair<'_, Rule>,
    memory: &mut MemoryManager,
    local_stack: &HashMap<String, Box<dyn Memory>>,
    globals: &HashSet<String>,
    strings: &mut Vec<String>,
) -> Vec<ProgramItem> {
    let mut pairs = pair.into_inner();

    let ident = pairs.next().unwrap();

    if pairs.len() > ARGUMENT_REGISTERS.len() {
        panic!("Too many arguments!");
    }

    let args = pairs.next().unwrap().into_inner();

    let mems = (0..args.len())
        .map(|_| memory.next_free_memory())
        .collect::<Vec<_>>();

    args.zip(mems.clone())
        .flat_map(|(arg, mem)| {
            handle_expression(
                arg.into_inner().next().unwrap(),
                memory,
                local_stack,
                globals,
                ExpressionDestination::Variable(RealizedVariable::Memory(mem.to_owned())),
                strings,
            )
        })
        .chain(vec![ProgramItem::FunctionCall {
            name: ident.as_str().to_owned(),
            args: mems,
        }])
        .collect()
}

fn handle_local_decl(
    pair: Pair<'_, Rule>,
    memory: &mut MemoryManager,
    local_stack: &mut HashMap<String, Box<dyn Memory>>,
    globals: &HashSet<String>,
) {
    let mut pairs = pair.into_inner();
    let _ty = pairs.next().unwrap().into_inner();

    // let num_indirection = ty
    //     .filter(|pair| matches!(pair.as_rule(), Rule::pointer))
    //     .count();

    let decl_ident_list = pairs.next().unwrap();

    for ident in decl_ident_list.into_inner() {
        if globals.iter().any(|g| g == ident.as_str())
            || local_stack.iter().any(|(l, _)| l == ident.as_str())
        {
            panic!(
                "Variable redeclaration error! Variable `{}` is defined more than once.",
                ident.as_str()
            );
        }

        // Allocate stack memory since &ident may happen
        local_stack.insert(ident.as_str().to_string(), memory.next_free_stack_memory());
    }
}

#[derive(Debug)]
enum ExpressionDestination {
    Variable(RealizedVariable),
    ConditionalJump(JumpDestination),
}

fn handle_assignment(
    pair: Pair<'_, Rule>,
    memory: &mut MemoryManager,
    local_stack: &HashMap<String, Box<dyn Memory>>,
    globals: &HashSet<String>,
    strings: &mut Vec<String>,
) -> Vec<ProgramItem> {
    let mut pairs = pair.into_inner();

    let dest = pairs.next().unwrap();

    let rv = match dest.as_rule() {
        Rule::array_access => {
            let mut pairs = dest.into_inner();

            let ident = pairs.next().unwrap();
            let base = get_variable_from_ident(local_stack, ident, globals);

            let offset_expressions = pairs.collect::<Vec<_>>();

            let (offsets, items): (Vec<_>, Vec<_>) = offset_expressions.into_iter().map(|expression| {
                let res = memory.next_free_stack_memory();
                let out = handle_expression(expression.into_inner().next().unwrap(), memory, local_stack, globals, ExpressionDestination::Variable(RealizedVariable::Memory(res.to_owned())), strings);
                (res, out)
            }).unzip();
            
            RealizedVariable::Offset { base: Box::new(base), offsets, items: items.into_iter().flatten().collect() }
        }
        Rule::ident_name => get_variable_from_ident(local_stack, dest, globals),
        _ => unreachable!(),
    };

    handle_expression(
        pairs.next().unwrap(),
        memory,
        local_stack,
        globals,
        ExpressionDestination::Variable(rv),
        strings,
    )
}

fn get_variable_from_ident(local_stack: &HashMap<String, Box<dyn Memory>>, ident: Pair<'_, Rule>, globals: &HashSet<String>) -> RealizedVariable {
    local_stack
        .iter()
        .find(|(lsv, _)| lsv.as_str() == ident.as_str().trim())
        .map(|(_, m)| RealizedVariable::Memory(m.to_owned()))
        .or_else(|| {
            globals
                .iter()
                .find(|g| g.as_str() == ident.as_str().trim())
                .map(|g| RealizedVariable::Global(g.to_owned()))
        })
        .expect("Undeclared variable!")
}

#[derive(Debug)]
struct ExpressionInfo<'a> {
    depth: usize,
    stack: Vec<ExpressionInstruction>,
    memory: &'a mut MemoryManager,
    jump_destination: Option<JumpDestination>,
    pre_execution_code: Vec<ProgramItem>,
}

impl ExpressionInfo<'_> {
    fn generate_jump_destination(&self) -> JumpDestination {
        let identifier = Alphanumeric.sample_string(&mut rand::thread_rng(), 16);
        JumpDestination {
            then: Some(format!("__{}_then", &identifier)),
            end: format!("__{}_end", &identifier),
        }
    }
}

#[derive(Debug)]
struct ExpressionInstruction {
    op: Operation,
    arg1: Operand,
    arg2: Operand,
}

impl ExpressionInstruction {
    fn write<W: Write>(self, writer: &mut W) -> Result<(), std::io::Error> {
        self.op.write(writer, self.arg1, self.arg2)
    }
}

#[derive(Debug)]
enum Operand {
    Memory(Box<dyn Memory>),
    DereferencedMemory(Box<dyn Memory>),
    Global(String),
    StringConstant(usize),
    IntegerConstant(i64),
    NoWrite,
}

impl ToString for Operand {
    fn to_string(&self) -> String {
        match self {
            Operand::Memory(m) => m.to_string(),
            Operand::DereferencedMemory(m) => {
                if m.is_register() {
                    format!("({})", m.to_string())
                } else {
                    m.to_string()
                }
            }
            Operand::Global(name) => format!("${name}"),
            Operand::StringConstant(i) => format!("$global_string_{i}"),
            Operand::IntegerConstant(i) => format!("${i}"),
            Operand::NoWrite => unreachable!(),
        }
    }
}

#[derive(Debug, Clone)]
enum Operation {
    Add,
    Sub,
    Mult,
    Div,
    Mod,
    Mov,
    /// Optimized version of CmpJmp for when the value is immediately being put into a variable instead of being used as a condition
    EqRel {
        op: EqRelOperation,
        store: Box<dyn Memory>,
    },
    CmpJmp {
        op: ComparisonOperation,
        dest: JumpDestination,
    },
    /// The destination for the previous CmpJmp operation
    CmpJmpDestination {
        op: ComparisonOperation,
        store: Box<dyn Memory>,
        dest: JumpDestination,
    },
}

impl Operation {
    fn write<W: Write>(
        self,
        writer: &mut W,
        arg1: Operand,
        mut arg2: Operand,
    ) -> Result<(), std::io::Error> {
        // The multiplication operations already use RAX for the operation, therefore they have a temp register built-in and don't need another temp
        let arg1 = if matches!(self, Operation::Div | Operation::Mod | Operation::Mult) {
            arg1
        } else {
            write_temp_register_if_needed(writer, arg1, &arg2)?
        };

        match self {
            Operation::Add => writer.write_all(
                format!("\taddq {}, {}\n", arg1.to_string(), arg2.to_string()).as_bytes(),
            ),
            Operation::Sub => {
                writer.write_all(
                    format!("\tsubq {}, {}\n", arg1.to_string(), arg2.to_string()).as_bytes(),
                )?;

                // I forgot how subtraction works but this seems to fix the problem
                // writer.write_all(format!("\tnegq {}\n", arg2.to_string()).as_bytes())?;

                Ok(())
            }
            Operation::Mult => {
                writer
                    .write_all(format!("\tmovq {}, %rax\n\tcqo\n", arg1.to_string()).as_bytes())?;
                writer.write_all(format!("\timulq {}\n", arg2.to_string()).as_bytes())?;
                writer.write_all(format!("\tmovq %rax, {}\n", arg2.to_string()).as_bytes())?;

                Ok(())
            }
            Operation::Div => {
                writer
                    .write_all(format!("\tmovq {}, %rax\n\tcqo\n", arg1.to_string()).as_bytes())?;
                writer.write_all(format!("\tidivq {}\n", arg2.to_string()).as_bytes())?;
                writer.write_all(format!("\tmovq %rax, {}\n", arg2.to_string()).as_bytes())?;

                Ok(())
            }
            Operation::Mod => {
                writer
                    .write_all(format!("\tmovq {}, %rax\n\tcqo\n", arg1.to_string()).as_bytes())?;
                writer.write_all(format!("\tidivq {}\n", arg2.to_string()).as_bytes())?;
                writer.write_all(format!("\tmovq %rdx, {}\n", arg2.to_string()).as_bytes())?;

                Ok(())
            }
            Operation::Mov => writer.write_all(
                format!("\tmovq {}, {}\n", arg1.to_string(), arg2.to_string()).as_bytes(),
            ),
            Operation::EqRel { op, store } => {
                writer.write_all(format!("\tcmpq {}, {}\n", arg2.to_string(), arg1.to_string()).as_bytes())?;

                let set_type = match op {
                    EqRelOperation::Eq => "setz",
                    EqRelOperation::Neq => "setnz",
                    EqRelOperation::Gt => "setg",
                    EqRelOperation::Lt => "setl",
                    EqRelOperation::Gte => "setge",
                    EqRelOperation::Lte => "setle",
                };

                writer.write_all(format!("\t{set_type} {}\n", store.to_string()).as_bytes())?;
                // This is only a precaution. Theoretically this shouldn't have any higher bytes, but I can't be sure in the future
                writer.write_all(format!("\tandq $1, {}\n", store.to_string()).as_bytes())?;

                Ok(())
            },
            Operation::CmpJmp { op, dest } => {
                if matches!(op, ComparisonOperation::And | ComparisonOperation::Or) {
                    // Normalize the values (the second value is always 0 or 1, so always normalized)
                    normalize_memory(writer, &mut arg2)?;
                }

                writer.write_all(
                    format!("\tcmpq {}, {}\n", arg2.to_string(), arg1.to_string()).as_bytes(),
                )?;

                let jump_type = match op {
                    ComparisonOperation::Eq => "jz",
                    ComparisonOperation::Neq
                    | ComparisonOperation::Or
                    | ComparisonOperation::And => "jnz",
                    ComparisonOperation::Gt => "jg",
                    ComparisonOperation::Lt => "jl",
                    ComparisonOperation::Gte => "jge",
                    ComparisonOperation::Lte => "jle",
                };

                if let Some(then) = &dest.then {
                    writer.write_all(format!("\t{jump_type} {then}\n").as_bytes())?;
                }

                Ok(())
            }
            Operation::CmpJmpDestination { op, store, dest } => {
                writer.write_all(
                    format!(
                        "\tmovq ${}, {}\n",
                        if matches!(op, ComparisonOperation::Or) {
                            0
                        } else {
                            1
                        },
                        store.to_string()
                    )
                    .as_bytes(),
                )?;
                writer.write_all(format!("\tjmp {}\n", dest.end).as_bytes())?;

                if let Some(then) = dest.then {
                    writer.write_all(format!("{}:\n", then).as_bytes())?;
                    writer.write_all(
                        format!(
                            "\tmovq ${}, {}\n",
                            if matches!(op, ComparisonOperation::Or) {
                                1
                            } else {
                                0
                            },
                            store.to_string()
                        )
                        .as_bytes(),
                    )?;
                }

                writer.write_all(format!("{}:\n", dest.end).as_bytes())?;

                Ok(())
            }
        }
    }
}

fn normalize_memory<W: Write>(writer: &mut W, mem: &mut Operand) -> Result<(), std::io::Error> {
    match *mem {
        Operand::Memory(_) => {}
        Operand::DereferencedMemory(_) => {}
        Operand::Global(_) => {}
        Operand::StringConstant(_) => panic!("Invalid comparison!"),
        Operand::IntegerConstant(c) => {
            *mem = Operand::IntegerConstant(if c == 0 { 0 } else { 1 });
            return Ok(());
        }
        Operand::NoWrite => unreachable!(),
    }

    writer.write_all(format!("\tcmpq $0, {}\n", mem.to_string()).as_bytes())?;
    writer.write_all(format!("\tsetnz {}\n", mem.to_string()).as_bytes())?;
    writer.write_all(format!("\tandq $1, {}\n", mem.to_string()).as_bytes())?;

    Ok(())
}

/// In case an instruction ends up needing multiple references (like `imulq -8(%rbx), -16(%rbx)`),
/// this will temporarily transfer the first value into %r15 (the SOURCE operand)
fn write_temp_register_if_needed<W: Write>(
    writer: &mut W,
    arg1: Operand,
    arg2: &Operand,
) -> Result<Operand, std::io::Error> {
    match arg1 {
        Operand::Memory(_) => match arg2 {
            Operand::Memory(m2) | Operand::DereferencedMemory(m2) => {
                if m2.is_register() {
                    return Ok(arg1);
                }

                writer.write_all(format!("\tmovq {}, %r15\n", arg1.to_string()).as_bytes())?;

                Ok(Operand::Memory(Box::new(CalleeSavedRegister::R15)))
            }
            _ => Ok(arg1),
        },
        Operand::DereferencedMemory(_) => match arg2 {
            Operand::Memory(m2) | Operand::DereferencedMemory(m2) => {
                if m2.is_register() {
                    return Ok(arg1);
                }

                writer.write_all(format!("\tmovq {}, %r15\n", arg1.to_string()).as_bytes())?;

                Ok(Operand::Memory(Box::new(CalleeSavedRegister::R15)))
            }
            _ => Ok(arg1),
        },
        _ => Ok(arg1),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ComparisonOperation {
    And,
    Or,
    Eq,
    Neq,
    Gt,
    Lt,
    Gte,
    Lte,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EqRelOperation {
    Eq,
    Neq,
    Gt,
    Lt,
    Gte,
    Lte,
}

#[derive(Debug, Clone)]
struct JumpDestination {
    then: Option<String>,
    end: String,
}

fn handle_expression(
    pair: Pair<'_, Rule>,
    memory: &mut MemoryManager,
    local_stack: &HashMap<String, Box<dyn Memory>>,
    globals: &HashSet<String>,
    // Where to try to jump if a JMP operation is necessary and succeeds
    destination: ExpressionDestination,
    strings: &mut Vec<String>,
) -> Vec<ProgramItem> {
    let jump_destination = match &destination {
        ExpressionDestination::Variable(_) => None,
        ExpressionDestination::ConditionalJump(jd) => Some(jd.to_owned()),
    };

    let mut expr_info = ExpressionInfo {
        memory,
        jump_destination,
        depth: 0,
        stack: vec![],
        pre_execution_code: vec![],
    };

    let expr = build_expression_stack(
        pair.into_inner().next().unwrap(),
        &mut expr_info,
        local_stack,
        globals,
        strings,
    );

    expr_info
        .pre_execution_code
        .into_iter()
        .chain(vec![ProgramItem::Expression {
            stack: expr_info.stack,
            output: expr,
            destination,
        }])
        .collect()
}

fn build_expression_stack(
    pair: Pair<'_, Rule>,
    info: &mut ExpressionInfo,
    local_stack: &HashMap<String, Box<dyn Memory>>,
    globals: &HashSet<String>,
    strings: &mut Vec<String>,
) -> Box<dyn Memory> {
    match pair.as_rule() {
        Rule::primary_expr => handle_primary_expression(pair, info, local_stack, globals, strings),
        Rule::logical_or_expr => variadic_expression_helper(
            pair,
            info,
            local_stack,
            globals,
            strings,
            ComparisonOperation::Or,
        ),
        Rule::logical_and_expr => variadic_expression_helper(
            pair,
            info,
            local_stack,
            globals,
            strings,
            ComparisonOperation::And,
        ),
        Rule::equality_expr => {
            eq_or_rel_expression_helper(pair, info, local_stack, globals, strings)
        }
        Rule::relational_expr => {
            eq_or_rel_expression_helper(pair, info, local_stack, globals, strings)
        }
        Rule::additive_expr => {
            mathematic_variadic_expression_helper(pair, info, local_stack, globals, strings)
        }
        Rule::multiplicative_expr => {
            mathematic_variadic_expression_helper(pair, info, local_stack, globals, strings)
        }
        _ => unreachable!(),
    }
}

fn handle_primary_expression(
    pair: Pair<'_, Rule>,
    info: &mut ExpressionInfo,
    local_stack: &HashMap<String, Box<dyn Memory>>,
    globals: &HashSet<String>,
    strings: &mut Vec<String>,
) -> Box<dyn Memory> {
    info.depth += 1;
    let pair = pair.into_inner().next().unwrap();
    match pair.as_rule() {
        Rule::literal => {
            let lit = pair.into_inner().next().unwrap();
            match lit.as_rule() {
                Rule::string => {
                    // Assuming nothing stupid is going on here,
                    // I should just be able to assume that the string is the only thing in the expression
                    strings.push(lit.as_str().to_string());
                    let next_loc = info.memory.next_free_memory();
                    info.stack.push(ExpressionInstruction {
                        op: Operation::Mov,
                        arg1: Operand::StringConstant(strings.len() - 1),
                        arg2: Operand::Memory(dyn_clone::clone_box(next_loc.as_ref())),
                    });
                    next_loc
                }
                Rule::integer => {
                    let next_loc = info.memory.next_free_memory();
                    info.stack.push(ExpressionInstruction {
                        op: Operation::Mov,
                        arg1: Operand::IntegerConstant(lit.as_str().trim().parse().unwrap()),
                        arg2: Operand::Memory(dyn_clone::clone_box(next_loc.as_ref())),
                    });
                    next_loc
                }
                _ => unreachable!(),
            }
        }
        Rule::call => {
            info.pre_execution_code.append(&mut handle_function_call(
                pair,
                info.memory,
                local_stack,
                globals,
                strings,
            ));

            let dest = info.memory.next_free_memory();

            info.stack.push(ExpressionInstruction {
                op: Operation::Mov,
                arg1: Operand::Memory(Box::new(UtilRegister::Rax)),
                arg2: Operand::Memory(dyn_clone::clone_box(dest.as_ref())),
            });

            dest
        }
        Rule::array_access => {
            let mut pairs = pair.into_inner();
            let ident = pairs.next().unwrap();

            let local_var = local_stack
                .iter()
                .find(|(lsv, _)| lsv.as_str() == ident.as_str().trim());

            if let Some((_, local_mem)) = local_var {
                info.stack.push(ExpressionInstruction { 
                    op: Operation::Mov, 
                    arg1: Operand::Memory(Box::new(UtilRegister::Rbp)), 
                    arg2: Operand::Memory(Box::new(CalleeSavedRegister::R15)) 
                });

                info.stack.push(ExpressionInstruction { 
                    op: Operation::Sub, 
                    arg1: Operand::IntegerConstant(local_mem.stack_offset() as i64), 
                    arg2: Operand::Memory(Box::new(CalleeSavedRegister::R15)) 
                });

                info.stack.push(ExpressionInstruction {
                    op: Operation::Mov,
                    arg1: Operand::DereferencedMemory(Box::new(CalleeSavedRegister::R15)),
                    arg2: Operand::Memory(Box::new(CalleeSavedRegister::R15)),
                });
            }

            let global_var = globals.iter().find(|g| g.as_str() == ident.as_str().trim());

            if let Some(global) = global_var {
                info.stack.push(ExpressionInstruction {
                    op: Operation::Mov,
                    arg1: Operand::Global(global.to_owned()),
                    arg2: Operand::Memory(Box::new(CalleeSavedRegister::R15)),
                });
                info.stack.push(ExpressionInstruction {
                    op: Operation::Mov,
                    arg1: Operand::DereferencedMemory(Box::new(CalleeSavedRegister::R15)),
                    arg2: Operand::Memory(Box::new(CalleeSavedRegister::R15)),
                });
            }

            if global_var.is_none() && local_var.is_none() {
                panic!("Undefined variable!");
            }

            let offset_expressions = pairs.collect::<Vec<_>>();

            for expression in offset_expressions {
                let es = build_expression_stack(expression.into_inner().next().unwrap(), info, local_stack, globals, strings);
                
                info.stack.push(ExpressionInstruction { 
                    op: Operation::Add, 
                    arg1: Operand::Memory(es), 
                    arg2: Operand::Memory(Box::new(CalleeSavedRegister::R15))
                });

                info.stack.push(ExpressionInstruction { 
                    op: Operation::Mov, 
                    arg1: Operand::DereferencedMemory(Box::new(CalleeSavedRegister::R15)), 
                    arg2: Operand::Memory(Box::new(CalleeSavedRegister::R15)) 
                });
            }

            let mem = info.memory.next_free_stack_memory();

            info.stack.push(ExpressionInstruction { 
                op: Operation::Mov, 
                arg1: Operand::Memory(Box::new(CalleeSavedRegister::R15)), 
                arg2: Operand::Memory(mem.to_owned()) 
            });

            mem
        },
        Rule::expression => build_expression_stack(
            pair.into_inner().next().unwrap(),
            info,
            local_stack,
            globals,
            strings,
        ),
        Rule::ident => {
            let mut pairs = pair.into_inner();
            let address_of = pairs.len() == 2;
            if address_of {
                let _ = pairs.next();
            }

            let pair = pairs.next().unwrap();

            let local_var = local_stack
                .iter()
                .find(|(lsv, _)| lsv.as_str() == pair.as_str().trim());

            if let Some((_, local_mem)) = local_var {
                // Inefficient as fuck, but fixes issues where multiplying the same local together caused register collisions
                let mem = info.memory.next_free_memory();
                if address_of {
                    info.stack.push(ExpressionInstruction { 
                        op: Operation::Mov, 
                        arg1: Operand::Memory(Box::new(UtilRegister::Rbp)), 
                        arg2: Operand::Memory(mem.to_owned()) 
                    });

                    info.stack.push(ExpressionInstruction { 
                        op: Operation::Sub, 
                        arg1: Operand::IntegerConstant(local_mem.stack_offset() as i64), 
                        arg2: Operand::Memory(mem.to_owned()) 
                    });
                } else {
                    info.stack.push(ExpressionInstruction {
                        op: Operation::Mov,
                        arg1: Operand::Memory(local_mem.to_owned()),
                        arg2: Operand::Memory(mem.to_owned()),
                    });
                }

                return mem;
            }

            let global_var = globals.iter().find(|g| g.as_str() == pair.as_str().trim());

            if let Some(global) = global_var {
                // Deref the global into R15, then write it to some other place in memory to make sure another global load can't overwrite it
                let mem = info.memory.next_free_memory();
                if address_of {
                    info.stack.push(ExpressionInstruction { 
                        op: Operation::Mov, 
                        arg1: Operand::Global(global.to_owned()), 
                        arg2: Operand::Memory(mem.to_owned()) 
                    });
                } else {
                    info.stack.push(ExpressionInstruction {
                        op: Operation::Mov,
                        arg1: Operand::Global(global.to_owned()),
                        arg2: Operand::Memory(Box::new(CalleeSavedRegister::R15)),
                    });
                    info.stack.push(ExpressionInstruction {
                        op: Operation::Mov,
                        arg1: Operand::DereferencedMemory(Box::new(CalleeSavedRegister::R15)),
                        arg2: Operand::Memory(Box::new(CalleeSavedRegister::R15)),
                    });
                    info.stack.push(ExpressionInstruction {
                        op: Operation::Mov,
                        arg1: Operand::Memory(Box::new(CalleeSavedRegister::R15)),
                        arg2: Operand::Memory(mem.to_owned()),
                    });
                }

                return mem;
            }

            panic!("Undefined variable `{}`!", pair.as_str().trim());
        }
        _ => unreachable!(),
    }
}

fn mathematic_variadic_expression_helper(
    pair: Pair<'_, Rule>,
    info: &mut ExpressionInfo,
    local_stack: &HashMap<String, Box<dyn Memory>>,
    globals: &HashSet<String>,
    strings: &mut Vec<String>,
) -> Box<dyn Memory> {
    let mut pairs = pair.into_inner();
    if pairs.len() == 1 {
        return build_expression_stack(pairs.next().unwrap(), info, local_stack, globals, strings);
    }

    info.depth += 1;

    // Convert the pairs to postfix
    let pairs = {
        let mut stack = VecDeque::new();
        let mut expression = Vec::new();

        fn is_higher_precendence(challenger: Rule, incumbent: Rule) -> bool {
            match challenger {
                Rule::mult_type => true,
                Rule::add_type => matches!(incumbent, Rule::add_type),
                _ => unreachable!(),
            }
        }

        for pair in pairs {
            match pair.as_rule() {
                Rule::add_type | Rule::mult_type => {
                    if stack
                        .back()
                        .is_some_and(|last_stack_item: &Pair<'_, Rule>| {
                            is_higher_precendence(last_stack_item.as_rule(), pair.as_rule())
                        })
                    {
                        // New operator has lower precedence, start popping until it doesn't
                        while stack
                            .back()
                            .is_some_and(|last_stack_item: &Pair<'_, Rule>| {
                                is_higher_precendence(last_stack_item.as_rule(), pair.as_rule())
                            })
                        {
                            expression.push(stack.pop_back().unwrap());
                        }

                        stack.push_back(pair);
                    } else {
                        // New operator has higher precedence, add it to the stack
                        stack.push_back(pair);
                    }
                }
                _ => expression.push(pair),
            }
        }

        // Empty the stack
        while let Some(back) = stack.pop_back() {
            expression.push(back);
        }

        expression
    };

    #[derive(Debug, Clone)]
    enum StackEvaluationStep {
        Memory(Box<dyn Memory>),
        Expression(
            Operation,
            Box<StackEvaluationStep>,
            Box<StackEvaluationStep>,
        ),
    }

    // Parse the arguments and symbols
    let mut sub_expressions = VecDeque::new();
    for item in pairs {
        match item.as_rule() {
            Rule::add_type | Rule::mult_type => {
                let top = sub_expressions.pop_back().expect("Invalid expression!");
                let second = sub_expressions.pop_back().expect("Invalid expression!");

                let op = match item.as_str() {
                    "*" => Operation::Mult,
                    "/" => Operation::Div,
                    "%" => Operation::Mod,
                    "+" => Operation::Add,
                    "-" => Operation::Sub,
                    _ => unreachable!(),
                };

                // Gotta switch subtraction for some reason, everything else works fine?
                let (top, second) = if matches!(op, Operation::Sub) {
                    (second, top)
                } else {
                    (top, second)
                };

                sub_expressions.push_back(StackEvaluationStep::Expression(
                   op,
                    Box::new(second),
                    Box::new(top),
                ));
            }
            _ => sub_expressions.push_back(StackEvaluationStep::Memory(build_expression_stack(
                item,
                info,
                local_stack,
                globals,
                strings,
            ))),
        }
    }

    fn convert_subexpression_to_operations(
        info: &mut ExpressionInfo,
        sub_expression: Box<StackEvaluationStep>,
    ) -> Box<dyn Memory> {
        match sub_expression.as_ref() {
            StackEvaluationStep::Memory(memory) => memory.clone(),
            StackEvaluationStep::Expression(op, arg1, arg2) => {
                let arg1 = convert_subexpression_to_operations(info, arg1.clone());
                let arg2 = convert_subexpression_to_operations(info, arg2.clone());

                info.stack.push(ExpressionInstruction {
                    op: op.to_owned(),
                    arg1: Operand::Memory(arg1),
                    arg2: Operand::Memory(dyn_clone::clone_box(arg2.as_ref())),
                });

                arg2
            }
        }
    }

    // Convert the subexpressions into expression operations that can be evaluated and written
    // Using an inside out traversal, this can be done pretty easily

    convert_subexpression_to_operations(info, Box::new(sub_expressions.pop_front().unwrap()))
}

/// This function requires that some JMP instruction exists, otherwise it creates one itself
fn eq_or_rel_expression_helper(
    pair: Pair<'_, Rule>,
    info: &mut ExpressionInfo,
    local_stack: &HashMap<String, Box<dyn Memory>>,
    globals: &HashSet<String>,
    strings: &mut Vec<String>,
) -> Box<dyn Memory> {
    let mut pairs = pair.into_inner();
    if pairs.len() == 1 {
        return build_expression_stack(pairs.next().unwrap(), info, local_stack, globals, strings);
    }

    info.depth += 1;

    let left_operand =
        build_expression_stack(pairs.next().unwrap(), info, local_stack, globals, strings);
    let (eop, cop) = match pairs.next().unwrap().as_str() {
        "==" => (EqRelOperation::Eq, ComparisonOperation::Eq),
        "!=" => (EqRelOperation::Neq, ComparisonOperation::Neq),
        ">" => (EqRelOperation::Gt, ComparisonOperation::Gt),
        "<" => (EqRelOperation::Lt, ComparisonOperation::Lt),
        ">=" => (EqRelOperation::Gte, ComparisonOperation::Gte),
        "<=" => (EqRelOperation::Lte, ComparisonOperation::Lte),
        _ => unreachable!(),
    };
    let right_operand =
        build_expression_stack(pairs.next().unwrap(), info, local_stack, globals, strings);

    let mem = info.memory.next_free_memory();

    let has_jump = info.jump_destination.is_some();

    info.stack.push(ExpressionInstruction {
        op: if has_jump {
            Operation::CmpJmp {
                op: cop,
                dest: info
                    .jump_destination
                    .clone()
                    .take()
                    .unwrap(),
            }
        } else {
            Operation::EqRel { op: eop, store: dyn_clone::clone_box(mem.as_ref()) }
        },
        arg1: Operand::Memory(left_operand),
        arg2: Operand::Memory(right_operand),
    });

    if has_jump {
        info.stack.push(ExpressionInstruction {
            op: Operation::CmpJmpDestination {
                op: cop,
                store: dyn_clone::clone_box(mem.as_ref()),
                dest: info
                    .jump_destination
                    .clone()
                    .take()
                    .unwrap(),
            },
            arg1: Operand::NoWrite,
            arg2: Operand::NoWrite,
        });
    }

    mem
}

fn variadic_expression_helper(
    pair: Pair<'_, Rule>,
    info: &mut ExpressionInfo,
    local_stack: &HashMap<String, Box<dyn Memory>>,
    globals: &HashSet<String>,
    strings: &mut Vec<String>,
    op: ComparisonOperation,
) -> Box<dyn Memory> {
    let mut pairs = pair.into_inner();
    if pairs.len() == 1 {
        return build_expression_stack(pairs.next().unwrap(), info, local_stack, globals, strings);
    }

    info.depth += 1;

    let mut ops = VecDeque::new();
    for ops_item in pairs {
        ops.push_back(build_expression_stack(
            ops_item,
            info,
            local_stack,
            globals,
            strings,
        ));
    }

    // All of these calls should realistically jump to the same place
    // Result storage will happen regardless of whether it's needed because this is a single-pass compiler
    let dest = info
        .jump_destination
        .take()
        .unwrap_or_else(|| info.generate_jump_destination());
    let final_result = info.memory.next_free_memory();

    // let mut comparison_register = ops.pop_back().unwrap();
    while let Some(op_mem) = ops.pop_back() {
        // If needed, allocate a new JMP destination and register to store the result
        // If this is the last instruction to be generated, then take the one out of `info` if it exists
        // let dest = if !ops.is_empty() {
        //     info.generate_jump_destination()
        // } else {
        //     info.jump_destination.take().unwrap_or_else(|| info.generate_jump_destination())
        // };
        // let next_result = info.memory.next_free_memory();

        info.stack.push(ExpressionInstruction {
            op: Operation::CmpJmp {
                op,
                dest: dest.clone(),
            },
            arg1: Operand::Memory(op_mem),
            arg2: if op == ComparisonOperation::And {
                Operand::IntegerConstant(1)
            } else {
                Operand::IntegerConstant(0)
            },
        });

        // comparison_register = next_result;
    }

    info.stack.push(ExpressionInstruction {
        op: Operation::CmpJmpDestination {
            op,
            store: dyn_clone::clone_box(final_result.as_ref()),
            dest: dest.clone(),
        },
        arg1: Operand::NoWrite,
        arg2: Operand::NoWrite,
    });

    // comparison_register
    final_result
}
