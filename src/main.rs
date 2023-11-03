use std::{
    collections::{HashSet, VecDeque},
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

#[derive(Debug, ClapParser)]
struct Args {
    /// The output file
    #[arg(short, default_value = "a.s")]
    output: String,

    /// The SimpleC file to compile
    file: String,
}

#[derive(Debug, Parser)]
#[grammar = "simplec.pest"]
struct SimpleCParser;

// #[derive(Debug, Clone, Copy)]
// enum StackRegister {
//     Rsp,
//     Rbp,
// }

// impl ToString for StackRegister {
//     fn to_string(&self) -> String {
//         match self {
//             StackRegister::Rsp => "rsp",
//             StackRegister::Rbp => "rbp",
//         }.to_string()
//     }
// }

/// Any place you can store to and retrieve from
/// Examples include Registers, the Stack, and RAM
trait Memory: ToString + Debug + DynClone {}

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

impl Memory for CalleeSavedRegister {}

impl ToString for CalleeSavedRegister {
    fn to_string(&self) -> String {
        match self {
            CalleeSavedRegister::Rbx => "rbx",
            CalleeSavedRegister::R10 => "r10",
            CalleeSavedRegister::R13 => "r13",
            CalleeSavedRegister::R14 => "r14",
            CalleeSavedRegister::R15 => "r15",
        }
        .to_string()
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

impl Memory for ArgumentRegister {}

impl ToString for ArgumentRegister {
    fn to_string(&self) -> String {
        match self {
            ArgumentRegister::Rdi => "rdi",
            ArgumentRegister::Rsi => "rsi",
            ArgumentRegister::Rdx => "rdx",
            ArgumentRegister::Rcx => "rcx",
            ArgumentRegister::R8 => "r8",
            ArgumentRegister::R9 => "r9",
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
        args: HashSet<String>,
        children: Vec<ProgramItem>,
    },
    FunctionCall {
        name: String,
        args: Vec<ProgramItem>,
    },
    StringLiteralLoad {
        id: usize,
        target: Box<dyn Memory>,
    },
    Expression {
        inner: (),
        target: Box<dyn Memory>,
    },
}

// #[derive(Debug)]
// enum Expression {
//     Variable(Variable),
//     ArrayAccess {
//         variable: Variable,
//         offset: Box<Expression>,
//     },
//     StringConstant(usize),
//     IntegerConstant(i64),
//     Product(Vec<Expression>),
//     Sum(Vec<Expression>),
//     Difference(Vec<Expression>),
//     Quotient(Vec<Expression>),
//     Modulus(Vec<Expression>),
//     LogicalAnd(Vec<Expression>),
//     LogicalOr(Vec<Expression>),
//     Equal(Box<Expression>, Box<Expression>),
//     NotEqual(Box<Expression>, Box<Expression>),
//     Greater(Box<Expression>, Box<Expression>),
//     Less(Box<Expression>, Box<Expression>),
//     GreaterEq(Box<Expression>, Box<Expression>),
//     LessEq(Box<Expression>, Box<Expression>),
// }

impl ProgramItem {
    fn write<W: Write>(&self, writer: &mut W) -> Result<(), std::io::Error> {
        match self {
            ProgramItem::Global(name) => {
                writer.write_all(format!(".data\n\t.comm {name}, 8\n").as_bytes())
            }
            ProgramItem::Function {
                name,
                args,
                children,
            } => {
                // Header
                writer.write_all(format!(".text\n.globl {name}\n{name}:\n").as_bytes())?;

                // Frame pointer
                writer.write_all("\tpushq %rbp\n\tmovq %rsp, %rbp\n".as_bytes())?;

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
                    writer.write_all(format!("\tpushq %{}\n", register.to_string()).as_bytes())?;
                }

                // Content
                for child in children {
                    child.write(writer)?;
                }

                // Restore registers
                callee_saved.reverse();
                for register in &callee_saved {
                    writer.write_all(format!("\tpopq %{}\n", register.to_string()).as_bytes())?;
                }

                // Leave and return
                writer.write_all("\tleave\n\tret\n".as_bytes())?;

                Ok(())
            }
            Self::FunctionCall { name, args } => {
                assert!(
                    args.len() <= ARGUMENT_REGISTERS.len(),
                    "More args than supported for function `{name}`"
                );

                for src in args.iter() {
                    // writer.write_all(format!("\tmovq %{} %{}\n", src.to_string(), dest.to_string()).as_bytes())?;
                    src.write(writer)?;
                }

                // Safety for variadics if called
                writer.write_all("\txorq %rax, %rax\n".as_bytes())?;

                writer.write_all(format!("call {name}\n").as_bytes())?;

                Ok(())
            }
            Self::StringLiteralLoad { id, target } => {
                writer.write_all(
                    format!("\tmovq $global_string_{id}, %{}", target.to_string()).as_bytes(),
                )?;

                Ok(())
            }
            Self::Expression { inner, target } => todo!(),
        }
    }
}

fn main() {
    let args = Args::parse();

    let file = fs::read_to_string(args.file);

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

    let file = fs::File::create(args.output);

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
            .write_all(format!(".data\nglobal_string_{i}:\n\t.string \"{value}\"\n").as_bytes())
            .unwrap();
    }

    writer.flush().unwrap();
}

/// Handle potentially multiple globals
fn handle_global_decl(pair: Pair<'_, Rule>, globals: &mut HashSet<Variable>) -> Vec<ProgramItem> {
    let mut pairs = pair.into_inner();
    let ty = pairs.next().unwrap().into_inner();

    let num_indirection = ty
        .filter(|pair| matches!(pair.as_rule(), Rule::pointer))
        .count();

    let decl_ident_list = pairs.next().unwrap();

    decl_ident_list
        .into_inner()
        .map(|ident| {
            let ident = ident.as_str().to_string();

            if globals.iter().any(|g| g.name == ident.as_str()) {
                panic!(
                    "Variable redeclaration error! Variable `{}` is defined more than once.",
                    ident.as_str()
                );
            }

            globals.insert(Variable {
                name: ident.clone(),
                indirection: num_indirection,
            });

            ProgramItem::Global(ident)
        })
        .collect()
}

struct MemoryManager {}

#[derive(Debug, Clone)]
struct Variable {
    name: String,
    indirection: usize,
}

impl Eq for Variable {}

impl PartialEq for Variable {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl Hash for Variable {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

fn handle_function(
    pair: Pair<'_, Rule>,
    globals: &HashSet<Variable>,
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
        HashSet::new()
    };

    let statements = if args_list_is_statements {
        arg_list
    } else {
        pairs.next()
    };

    let mut local_stack = Vec::<Variable>::new();

    // Function may not have a body
    let children = if let Some(statements) = statements {
        statements
            .into_inner()
            .flat_map(|statement| match statement.as_rule() {
                Rule::decl => {
                    handle_local_decl(statement, &mut local_stack, globals);
                    vec![]
                }
                Rule::assignment => handle_assignment(statement, strings),
                Rule::call => todo!(),
                Rule::if_expr => todo!(),
                Rule::while_expr => todo!(),
                Rule::do_while_expr => todo!(),
                Rule::for_expr => todo!(),
                Rule::flow_control => todo!(),
                _ => unreachable!(),
            })
            .collect()
    } else {
        vec![]
    };

    ProgramItem::Function {
        name: ident.to_string(),
        args: arg_list_str,
        children,
    }
}

fn handle_local_decl(
    pair: Pair<'_, Rule>,
    local_stack: &mut Vec<Variable>,
    globals: &HashSet<Variable>,
) {
    let mut pairs = pair.into_inner();
    let ty = pairs.next().unwrap().into_inner();

    let num_indirection = ty
        .filter(|pair| matches!(pair.as_rule(), Rule::pointer))
        .count();

    let decl_ident_list = pairs.next().unwrap();

    for ident in decl_ident_list.into_inner() {
        if globals.iter().any(|g| g.name == ident.as_str())
            || local_stack.iter().any(|l| l.name == ident.as_str())
        {
            panic!(
                "Variable redeclaration error! Variable `{}` is defined more than once.",
                ident.as_str()
            );
        }

        local_stack.push(Variable {
            name: ident.as_str().to_string(),
            indirection: num_indirection,
        })
    }
}

fn handle_assignment(pair: Pair<'_, Rule>, strings: &mut Vec<String>) -> Vec<ProgramItem> {
    let mut pairs = pair.into_inner();

    let _dest = pairs.next().unwrap();

    handle_expression(
        pairs.next().unwrap(),
        Box::new(ArgumentRegister::R8),
        strings,
    );
    todo!()
}

#[derive(Debug, Default)]
struct ExpressionInfo {
    depth: usize,
    pointer_vars: usize,
    stack: Vec<ExpressionInstruction>,
}

impl ExpressionInfo {
    fn next_open_memory_location(&mut self) -> Box<dyn Memory> {
        Box::new(CalleeSavedRegister::Rbx)
    }
}

#[derive(Debug)]
struct ExpressionInstruction {
    op: Operation,
    arg1: Operand,
    arg2: Operand,
}

#[derive(Debug)]
enum Operand {
    Register(Box<dyn Memory>),
    Global(String),
    StringConstant(usize),
    IntegerConstant(i64),
}

#[derive(Debug, Clone, Copy)]
enum Operation {
    Add,
    Sub,
    Mult,
    Div,
    Mod,
    And,
    Or,
    Eq,
    Neq,
    Gt,
    Lt,
    Gte,
    Lte,
    Mov,
}

fn handle_expression(
    pair: Pair<'_, Rule>,
    destination: Box<dyn Memory>,
    strings: &mut Vec<String>,
) -> ProgramItem {
    let mut expr_info = ExpressionInfo::default();
    let expr = build_expression_stack(pair.into_inner().next().unwrap(), &mut expr_info, strings);
    println!("INFO: {:#?}", expr_info);
    println!("TARGET: {:#?}", expr);

    // ProgramItem::Expression { inner: expr, target: destination }
    todo!()
}

fn build_expression_stack(
    pair: Pair<'_, Rule>,
    info: &mut ExpressionInfo,
    strings: &mut Vec<String>,
) -> Box<dyn Memory> {
    match pair.as_rule() {
        Rule::primary_expr => handle_primary_expression(pair, info, strings),
        Rule::logical_or_expr => variadic_expression_helper(pair, info, strings, Operation::Or),
        Rule::logical_and_expr => variadic_expression_helper(pair, info, strings, Operation::And),
        Rule::equality_expr => eq_or_rel_expression_helper(pair, info, strings),
        Rule::relational_expr => eq_or_rel_expression_helper(pair, info, strings),
        Rule::additive_expr => four_function_variadic_expression_helper(pair, info, strings),
        Rule::multiplicative_expr => four_function_variadic_expression_helper(pair, info, strings),
        _ => unreachable!(),
    }
}

fn handle_primary_expression(
    pair: Pair<'_, Rule>,
    info: &mut ExpressionInfo,
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
                    let next_loc = info.next_open_memory_location();
                    info.stack.push(ExpressionInstruction {
                        op: Operation::Mov,
                        arg1: Operand::StringConstant(strings.len() - 1),
                        arg2: Operand::Register(dyn_clone::clone_box(next_loc.as_ref())),
                    });
                    next_loc
                }
                Rule::integer => {
                    let next_loc = info.next_open_memory_location();
                    info.stack.push(ExpressionInstruction {
                        op: Operation::Mov,
                        arg1: Operand::IntegerConstant(lit.as_str().trim().parse().unwrap()),
                        arg2: Operand::Register(dyn_clone::clone_box(next_loc.as_ref())),
                    });
                    next_loc
                }
                _ => unreachable!(),
            }
        }
        Rule::call => todo!(),
        Rule::array_access => todo!(),
        Rule::expression => {
            build_expression_stack(pair.into_inner().next().unwrap(), info, strings)
        }
        Rule::ident => todo!(),
        _ => unreachable!(),
    }
}

fn four_function_variadic_expression_helper(
    pair: Pair<'_, Rule>,
    info: &mut ExpressionInfo,
    strings: &mut Vec<String>,
) -> Box<dyn Memory> {
    let mut pairs = pair.into_inner();
    if pairs.len() == 1 {
        return build_expression_stack(pairs.next().unwrap(), info, strings);
    }

    info.depth += 1;

    todo!()
}

fn eq_or_rel_expression_helper(
    pair: Pair<'_, Rule>,
    info: &mut ExpressionInfo,
    strings: &mut Vec<String>,
) -> Box<dyn Memory> {
    let mut pairs = pair.into_inner();
    if pairs.len() == 1 {
        return build_expression_stack(pairs.next().unwrap(), info, strings);
    }

    info.depth += 1;

    todo!()
}

fn variadic_expression_helper(
    pair: Pair<'_, Rule>,
    info: &mut ExpressionInfo,
    strings: &mut Vec<String>,
    op: Operation,
) -> Box<dyn Memory> {
    let mut pairs = pair.into_inner();
    if pairs.len() == 1 {
        return build_expression_stack(pairs.next().unwrap(), info, strings);
    }

    info.depth += 1;

    let mut ops = VecDeque::new();
    for ops_item in pairs {
        ops.push_back(build_expression_stack(ops_item, info, strings));
    }

    let result_reg = ops.pop_front().unwrap();
    for op_mem in ops {
        info.stack.push(ExpressionInstruction {
            op,
            arg1: Operand::Register(op_mem),
            arg2: Operand::Register(dyn_clone::clone_box(result_reg.as_ref())),
        })
    }

    result_reg
}
