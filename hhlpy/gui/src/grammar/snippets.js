import {snippetCompletion as snip} from "@codemirror/autocomplete"

/// A collection of JavaScript-related
/// [snippets](#autocomplete.snippet).
export const snippets = [
  snip("@${var}${}", {
      label: "variable command",
      type: "keyword"
  }),
  snip("skip${}", {
    label: "skip",
    type: "keyword"
  }),
  snip("wait (${expr})${}", {
    label: "wait",
    type: "keyword"
  }),
  snip("${var} := ${expr}${}", {
    label: "assign",
    type: "keyword"
  }),
  snip("assert(${cond})${}", {
    label: "assert",
    type: "keyword"
  }),
  snip("test(${cond})${}", {
    label: "test",
    type: "keyword"
  }),
  snip("log(${cond})${}", {
    label: "log",
    type: "keyword"
  }),
  snip("( ${skip} )**${}", {
    label: "repeat",
    type: "keyword"
  }),
  snip("( ${skip} ){${true}}**${}", {
    label: "repeat",
    detail: "with condition",
    type: "keyword"
  }),
  snip("( ${skip} )**@invariant(${true})${}", {
    label: "repeat",
    detail: "with invariant",
    type: "keyword"
  }),
  snip("( ${skip} ){${true}}**@invariant(${true})${}", {
    label: "repeat",
    detail: "with invariant and condition",
    type: "keyword"
  }),
  snip("<${ode} & ${true}>${}", {
    label: "ODE",
    type: "keyword"
  }),
  snip("< & ${true}> |> [] ( ${interrupt} ) ${}", {
    label: "ODE",
    detail: "constant with interrupt",
    type: "keyword"
  }),
  snip("<${ode} & ${true}> |> [] ( ${interrupt} ) ${}", {
    label: "ODE",
    detail: "with interrupt",
    type: "keyword"
  }),
  snip("rec ${var} .( ${skip} )${}", {
    label: "rec",
    type: "keyword"
  }),
  snip("if ${true} then\n\t${skip}\nelse\n\t${skip}\nendif${}", {
    label: "If then else",
    type: "keyword"
  }),
//   VarCmd { "@" CNAME }
//   | SkipCmd { "skip" }
//   | WaitCmd { "wait" "(" expr ")" }
//   | AssignCmd { atom_expr ":=" expr }
//   | MultiAssignCmd { "(" lname ("," lname)+ ")" ":=" expr } // TODO: used + instead * here to avoid abiguity
//   | RandomAssignCmd { atom_expr ":=" "{" cond "}" }
//   | AssertCmd { "assert" "(" cond ("," expr)* ")" }
//   | TestCmd { "test" "(" cond ("," expr)* ")" }
//   | LogCmd { "log" "(" expr ("," expr)* ")" }
//   | comm_cmd
//   | RepeatCmd { "(" cmd ")**" }
//   | RepeatCondCmd { "(" cmd "){" cond "}**" }
//   | RepeatCmdInv { "(" cmd ")**@invariant(" cond ")" }
//   | RepeatCondCmdInv { "(" cmd "){" cond "}**@invariant(" cond ")" }
//   | Ode { "<" ode_seq "&" cond ">" }
//   | OdeCommConst { "<" "&" cond ">" "|>" "[]" "(" interrupt ")" }
//   | OdeComm { "<" ode_seq "&" cond ">" "|>" "[]" "(" interrupt ")" } 
//   | RecCmd { "rec" CNAME ".(" cmd ")" }
//   | IteCmd { "if" cond "then" cmd ("elif" cond "then" cmd)* "else" cmd "endif" }
//   | ParenCmd { "(" cmd ")" }
]