use crate::ast::*;

use pest::iterators::Pair;
use pest::Parser;

pub fn parse_polynomial(source: &str) -> Result<Polynomial, String> {
    match PilParser::parse(Rule::polynomial, source) {
        Ok(mut pairs) => {
            let mut next_identifier = 1u64;
            Ok(Polynomial::from(pairs.next().unwrap()))
        }
        Err(error) => Err(format!("{}", error)),
    }
}

pub fn parse_expression(source: &str) -> Result<Expression, String> {
    match PilParser::parse(Rule::expression, source) {
        Ok(mut pairs) => {
            let mut next_identifier = 1u64;
            Ok(Expression::from(pairs.next().unwrap()))
        }
        Err(error) => Err(format!("{}", error)),
    }
}

#[derive(Parser)]
#[grammar = "parser/pil.pest"]
struct PilParser;

pub struct Polynomial {
    name: String,
    definition: Expression,
}

pub enum Expression {
    Sum(Vec<Expression>),
    Difference(VecBox<Expression>, Box<Expression>),
    Product(Box<Expression>, Box<Expression>),
    ArrayAccess(String, usize),
    Identifier(String),
    Literal(String)
}

impl Polynomial {
    fn from(pair: Pair<Rule>) -> Polynomial {
        let mut token_iter = pair.into_inner();
        let name = token_iter.next().unwrap().as_str().to_string();
        let definition = Expression::from(token_iter.next().unwrap());

        Polynomial {
            name,
            definition
        }
    }
}

impl Expression {
    fn from(pair: Pair<Rule>) -> Expression {
        match pair.as_rule() {
            Rule::expression => {
                let inner = pair.into_inner();
                if inner.count() == 1 {
                    Expression::from(inner.next().unwrap())
                } else {
                    Expression::Product()
                }

            }
            _ => panic!("Invalid rule")
        }
    }
}

// impl Identifier {
//     fn from(pair: Pair<Rule>, next_identifier: &mut u64) -> Identifier {
//         let span = pair.clone().into_span();
//         let location = Some(SourceLocation {
//             start: span.start(),
//             end: span.end(),
//         });

//         let name = pair.as_str().to_string();

//         // TOOD much nicer to call some function that returns the id
//         *next_identifier += 1;
//         Identifier {
//             id: IdentifierID::Declaration(*next_identifier),
//             name,
//             location,
//         }
//     }

//     fn from_reference(pair: Pair<Rule>) -> Identifier {
//         let span = pair.clone().into_span();
//         let location = Some(SourceLocation {
//             start: span.start(),
//             end: span.end(),
//         });

//         let name = pair.as_str().to_string();

//         Identifier {
//             id: IdentifierID::UnresolvedReference,
//             name,
//             location,
//         }
//     }

//     fn list(pair: Pair<Rule>, next_identifier: &mut u64) -> Vec<Identifier> {
//         let mut identifiers: Vec<Identifier> = vec![];
//         for p in pair.into_inner() {
//             match p.as_rule() {
//                 Rule::identifier => {
//                     identifiers.push(Identifier::from(p, next_identifier));
//                 }
//                 _ => unreachable!(),
//             }
//         }
//         identifiers
//     }

//     fn list_reference(pair: Pair<Rule>) -> Vec<Identifier> {
//         let mut identifiers: Vec<Identifier> = vec![];
//         for p in pair.into_inner() {
//             match p.as_rule() {
//                 Rule::identifier => {
//                     identifiers.push(Identifier::from_reference(p));
//                 }
//                 _ => unreachable!(),
//             }
//         }
//         identifiers
//     }
// }

// impl Literal {
//     fn from(pair: Pair<Rule>) -> Literal {
//         let span = pair.clone().into_span();
//         let location = Some(SourceLocation {
//             start: span.start(),
//             end: span.end(),
//         });

//         let mut token_iter = pair.into_inner();
//         let literal = token_iter.next().unwrap().as_str().to_string();

//         Literal { literal, location }
//     }
// }

// impl FunctionCall {
//     fn from(pair: Pair<Rule>, next_identifier: &mut u64) -> FunctionCall {
//         let span = pair.clone().into_span();
//         let location = Some(SourceLocation {
//             start: span.start(),
//             end: span.end(),
//         });

//         let mut token_iter = pair.into_inner();
//         let function = Identifier::from_reference(token_iter.next().unwrap());
//         let arguments = token_iter
//             .map(|p| match p.as_rule() {
//                 Rule::expression => Expression::from(p, next_identifier),
//                 _ => unreachable!(),
//             })
//             .collect();

//         FunctionCall {
//             function,
//             arguments,
//             location,
//         }
//     }
// }

// impl Expression {
//     fn from(pair: Pair<Rule>, next_identifier: &mut u64) -> Expression {
//         let mut token_iter = pair.into_inner();
//         let p = token_iter.next().unwrap();
//         match p.as_rule() {
//             Rule::function_call => Expression::FunctionCall(FunctionCall::from(p, next_identifier)),
//             Rule::identifier => Expression::Identifier(Identifier::from_reference(p)),
//             Rule::literal => Expression::Literal(Literal::from(p)),
//             _ => unreachable!(),
//         }
//     }
// }

// impl Case {
//     fn from(pair: Pair<Rule>, next_identifier: &mut u64) -> Case {
//         let span = pair.clone().into_span();
//         let location = Some(SourceLocation {
//             start: span.start(),
//             end: span.end(),
//         });

//         let mut token_iter = pair.into_inner();
//         let literal = Literal::from(token_iter.next().unwrap());
//         let body = Block::from(token_iter.next().unwrap(), next_identifier);

//         Case {
//             literal: Some(literal),
//             body,
//             location,
//         }
//     }

//     fn from_default(pair: Pair<Rule>, next_identifier: &mut u64) -> Case {
//         let span = pair.clone().into_span();
//         let location = Some(SourceLocation {
//             start: span.start(),
//             end: span.end(),
//         });

//         let mut token_iter = pair.into_inner();
//         let body = Block::from(token_iter.next().unwrap(), next_identifier);

//         Case {
//             literal: None,
//             body,
//             location,
//         }
//     }
// }

// impl Switch {
//     fn from(pair: Pair<Rule>, next_identifier: &mut u64) -> Switch {
//         let span = pair.clone().into_span();
//         let location = Some(SourceLocation {
//             start: span.start(),
//             end: span.end(),
//         });

//         let mut token_iter = pair.into_inner();
//         let expression = Expression::from(token_iter.next().unwrap(), next_identifier);
//         let cases = token_iter
//             .map(|p| match p.as_rule() {
//                 Rule::case => Case::from(p, next_identifier),
//                 Rule::default => Case::from_default(p, next_identifier),
//                 _ => unreachable!(),
//             })
//             .collect();

//         Switch {
//             expression,
//             cases,
//             location,
//         }
//     }
// }

// impl Assignment {
//     fn from(pair: Pair<Rule>, next_identifier: &mut u64) -> Assignment {
//         let span = pair.clone().into_span();
//         let location = Some(SourceLocation {
//             start: span.start(),
//             end: span.end(),
//         });

//         let mut token_iter = pair.into_inner();
//         let variables = Identifier::list_reference(token_iter.next().unwrap());
//         let value = Expression::from(token_iter.next().unwrap(), next_identifier);

//         Assignment {
//             variables,
//             value,
//             location,
//         }
//     }
// }

// impl VariableDeclaration {
//     fn from(pair: Pair<Rule>, next_identifier: &mut u64) -> VariableDeclaration {
//         let span = pair.clone().into_span();
//         let location = Some(SourceLocation {
//             start: span.start(),
//             end: span.end(),
//         });

//         let mut token_iter = pair.into_inner();

//         let variables = Identifier::list(token_iter.next().unwrap(), next_identifier);
//         let value = token_iter
//             .next()
//             .map(|e| Expression::from(e, next_identifier));

//         VariableDeclaration {
//             variables,
//             value,
//             location,
//         }
//     }
// }

// impl FunctionDefinition {
//     fn from(pair: Pair<Rule>, next_identifier: &mut u64) -> FunctionDefinition {
//         let span = pair.clone().into_span();
//         let location = Some(SourceLocation {
//             start: span.start(),
//             end: span.end(),
//         });

//         let mut token_iter = pair.into_inner();
//         let name = Identifier::from(token_iter.next().unwrap(), next_identifier);

//         let current = token_iter.next().unwrap();
//         let (parameters, current) = match current.as_rule() {
//             Rule::parameter_list => (
//                 Identifier::list(current, next_identifier),
//                 token_iter.next().unwrap(),
//             ),
//             _ => (vec![], current),
//         };
//         let (returns, current) = match current.as_rule() {
//             Rule::identifier_list => (
//                 Identifier::list(current, next_identifier),
//                 token_iter.next().unwrap(),
//             ),
//             _ => (vec![], current),
//         };
//         let body = Block::from(current, next_identifier);

//         FunctionDefinition {
//             name,
//             parameters,
//             returns,
//             body,
//             location,
//         }
//     }
// }

// impl If {
//     fn from(pair: Pair<Rule>, next_identifier: &mut u64) -> If {
//         let span = pair.clone().into_span();
//         let location = Some(SourceLocation {
//             start: span.start(),
//             end: span.end(),
//         });

//         let mut token_iter = pair.into_inner();
//         let condition = Expression::from(token_iter.next().unwrap(), next_identifier);
//         let body = Block::from(token_iter.next().unwrap(), next_identifier);

//         If {
//             condition,
//             body,
//             location,
//         }
//     }
// }

// impl ForLoop {
//     fn from(pair: Pair<Rule>, next_identifier: &mut u64) -> ForLoop {
//         let span = pair.clone().into_span();
//         let location = Some(SourceLocation {
//             start: span.start(),
//             end: span.end(),
//         });

//         let mut token_iter = pair.into_inner();
//         let pre = Block::from(token_iter.next().unwrap(), next_identifier);
//         let condition = Expression::from(token_iter.next().unwrap(), next_identifier);
//         let post = Block::from(token_iter.next().unwrap(), next_identifier);
//         let body = Block::from(token_iter.next().unwrap(), next_identifier);

//         ForLoop {
//             pre,
//             condition,
//             post,
//             body,
//             location,
//         }
//     }
// }

// impl Statement {
//     fn from(pair: Pair<Rule>, next_identifier: &mut u64) -> Statement {
//         let mut token_iter = pair.into_inner();
//         let p = token_iter.next().unwrap();
//         match p.as_rule() {
//             Rule::block => Statement::Block(Block::from(p, next_identifier)),
//             Rule::function_definition => {
//                 Statement::FunctionDefinition(FunctionDefinition::from(p, next_identifier))
//             }
//             Rule::variable_declaration => {
//                 Statement::VariableDeclaration(VariableDeclaration::from(p, next_identifier))
//             }
//             Rule::assignment => Statement::Assignment(Assignment::from(p, next_identifier)),
//             Rule::expression => Statement::Expression(Expression::from(p, next_identifier)),
//             Rule::switch => Statement::Switch(Switch::from(p, next_identifier)),
//             Rule::if_statement => Statement::If(If::from(p, next_identifier)),
//             Rule::for_loop => Statement::ForLoop(ForLoop::from(p, next_identifier)),
//             Rule::break_statement => Statement::Break,
//             Rule::continue_statement => Statement::Continue,
//             Rule::leave => Statement::Leave,
//             _ => unreachable!(),
//         }
//     }
// }

// impl Data {
//     fn from(pair: Pair<Rule>) -> Data {
//         let span = pair.clone().into_span();
//         let location = Some(SourceLocation {
//             start: span.start(),
//             end: span.end(),
//         });

//         let mut token_iter = pair.into_inner();
//         let name = token_iter.next().unwrap().as_str().to_string();
//         let data = token_iter.next().unwrap().as_str().to_string();

//         Data {
//             name,
//             data,
//             location,
//         }
//     }
// }

// impl Code {
//     fn from(pair: Pair<Rule>, next_identifier: &mut u64) -> Code {
//         let span = pair.clone().into_span();
//         let location = Some(SourceLocation {
//             start: span.start(),
//             end: span.end(),
//         });

//         let mut token_iter = pair.into_inner();
//         let body = Block::from(token_iter.next().unwrap(), next_identifier);

//         Code { body, location }
//     }
// }

// impl Object {
//     fn from(pair: Pair<Rule>, next_identifier: &mut u64) -> Object {
//         let span = pair.clone().into_span();
//         let location = Some(SourceLocation {
//             start: span.start(),
//             end: span.end(),
//         });

//         let mut token_iter = pair.into_inner();
//         let name = token_iter.next().unwrap().as_str().to_string();
//         let code = Code::from(token_iter.next().unwrap(), next_identifier);
//         let data = token_iter
//             .map(|p| match p.as_rule() {
//                 Rule::data => Data::from(p),
//                 _ => unreachable!(),
//             })
//             .collect();

//         Object {
//             name,
//             code,
//             location,
//             data,
//         }
//     }
// }

// impl Block {
//     fn from(pair: Pair<Rule>, next_identifier: &mut u64) -> Block {
//         let span = pair.clone().into_span();
//         let location = Some(SourceLocation {
//             start: span.start(),
//             end: span.end(),
//         });

//         let mut statements: Vec<Statement> = vec![];
//         for p in pair.into_inner() {
//             match p.as_rule() {
//                 Rule::statement => {
//                     statements.push(Statement::from(p, next_identifier));
//                 }
//                 _ => unreachable!(),
//             }
//         }

//         Block {
//             statements,
//             location,
//         }
//     }
// }

// impl Root {
//     fn from(pair: Pair<Rule>, next_identifier: &mut u64) -> Root {
//         let span = pair.clone().into_span();
//         let location = Some(SourceLocation {
//             start: span.start(),
//             end: span.end(),
//         });

//         let mut token_iter = pair.into_inner();
//         let p = token_iter.next().unwrap();
//         let inner = match p.as_rule() {
//             Rule::object => InnerRoot::Object(Object::from(p, next_identifier)),
//             Rule::block => InnerRoot::Block(Block::from(p, next_identifier)),
//             _ => unreachable!(),
//         };

//         Root { inner, location }
//     }
// }

// pub fn parse_block(source: &str) -> Result<Block, String> {
//     match parse_root(source)?.inner {
//         InnerRoot::Block(block) => Ok(block),
//         _ => unreachable!(),
//     }
// }

// pub fn parse_object(source: &str) -> Result<Object, String> {
//     match parse_root(source)?.inner {
//         InnerRoot::Object(obj) => Ok(obj),
//         _ => unreachable!(),
//     }
// }

// pub fn parse_expression(source: &str) -> Result<Expression, String> {
//     let block_source = format!("{{ {} }}", source);
//     match YulParser::parse(Rule::block, block_source.as_str()) {
//         Err(error) => Err(format!("{}", error)),
//         Ok(mut pairs) => {
//             let mut next_identifier = 1u64;
//             let mut block = Block::from(pairs.next().unwrap(), &mut next_identifier);
//             if let Statement::Expression(e) = block.statements.pop().unwrap() {
//                 Ok(e)
//             } else {
//                 panic!();
//             }
//         }
//     }
// }

// #[cfg(test)]
// mod tests {
//     use super::*;

//     use std::fs::read_to_string;

//     #[test]
//     fn continue_statement() {
//         test_file("examples/continue.yul");
//     }

//     #[test]
//     fn break_statement() {
//         test_file("examples/break.yul");
//     }

//     #[test]
//     fn for_loop() {
//         test_file("examples/for.yul");
//     }

//     #[test]
//     fn if_statement() {
//         test_file("examples/if_statement.yul");
//     }

//     #[test]
//     fn switch() {
//         test_file("examples/switch.yul");
//     }

//     #[test]
//     fn assignment() {
//         test_file("examples/assignment.yul");
//     }

//     #[test]
//     fn var_decl() {
//         test_file("examples/var_decl.yul");
//     }

//     #[test]
//     fn nested_blocks() {
//         test_file("examples/nested_blocks.yul");
//     }

//     #[test]
//     fn power_function_signature() {
//         test_file("examples/power_function_signature.yul");
//     }

//     #[test]
//     fn empty_block() {
//         test_file("examples/empty_block.yul");
//     }

//     #[test]
//     fn function_call() {
//         test_file("examples/function_call.yul");
//     }

//     #[test]
//     fn leave() {
//         test_file("examples/leave.yul");
//     }

//     #[test]
//     fn special_identifiers() {
//         test_file("examples/special_identifiers.yul");
//     }

//     #[test]
//     fn simple_object() {
//         test_file("examples/simple_object.yul");
//     }

//     #[test]
//     fn simple_object_with_data() {
//         test_file("examples/simple_object_with_data.yul");
//     }

//     #[test]
//     fn simple_object_multi_data() {
//         test_file("examples/simple_object_multi_data.yul");
//     }

//     #[test]
//     fn object_with_code() {
//         test_file("examples/object_with_code.yul");
//     }

//     #[test]
//     fn comments() {
//         let source = "{ /* abc */ let x // def\n := 7 }// xx";
//         let block = parse_block(source).unwrap();
//         assert_eq!(block.to_string(), "{ let x := 7 }");
//     }

//     fn test_file(filename: &str) {
//         let source = read_to_string(filename).unwrap();
//         let root = parse_root(&source).unwrap();
//         let root_str = root.to_string();
//         assert_eq!(
//             source, root_str,
//             "Parsing-re-printing mismatch:\nsource:\n{}\n-----\nre-printed:\n{}\n",
//             source, root_str
//         );
//     }
// }
