import {parser} from "./hcsp_parser"
import {LRLanguage, LanguageSupport, indentNodeProp, foldNodeProp, foldInside, continuedIndent} from "@codemirror/language"
import {styleTags, tags as t} from "@codemirror/highlight"
import {linter} from "@codemirror/lint"
import {annotationPlugin} from "../decoration/button"

export const HCSPLanguage = LRLanguage.define({
  parser: parser.configure({
    props: [
      indentNodeProp.add({
        WaitCmd: continuedIndent({except:/\)/}),
        AssignCmd: continuedIndent(),
        MultiAssignCmd: continuedIndent(),
        RandomAssignCmd: continuedIndent({except:/\)/}),
        AssertCmd: continuedIndent({except:/\)/}),
        TestCmd: continuedIndent({except:/\)/}),
        LogCmd: continuedIndent({except:/\)/}),
        RepeatCmd: continuedIndent({except:/\}\*/}),
        RepeatCondCmd: continuedIndent({except:/(\}*\(|\))/}),
        Ode: continuedIndent({except:/>/}),
        OdeCommConst: continuedIndent({except:/(>|\))/}),
        OdeComm: continuedIndent({except:/(>|\))/}),
        RecCmd: continuedIndent({except:/\}/}),
        IteCmd: continuedIndent({except:/(if|\}|\{)/}),
      }),
      foldNodeProp.add({
        IteCmd: foldInside,
        RepeatCmd: foldInside
      }),
      styleTags({
        CNAME: t.variableName,
        LineComment: t.lineComment,
        ESCAPED_STRING: t.string,
        SIGNED_NUMBER: t.number,
        "( )": t.paren,
        "{ }": t.paren,
        "if then else rec log test assert pre post": t.controlKeyword,
        "+ - %": t.operator,
        "| & -> <->": t.logicOperator,
        "> >= < <=" : t.compareOperator,
        "min max gcd" : t.operatorKeyword,
        "skip wait assert test log" : t.keyword
      })
    ]
  }),
  languageData: {
    commentTokens: {line: "#"},
    indentOnInput: /^\s*(\}|then|else|\)|>)$/
  }
})

export const HCSPLinter = linter((editorView) =>{
  console.log(editorView);

  let tree = parser.parse(editorView.state.doc.toString())
  let cursor = tree.cursor()
  let diags = []
  do {
    if (cursor.type.isError) {
      diags.push({
        from: cursor.from,
        to: cursor.to,
        message: "Error",
        severity: "error",
      })
    }
  } while (cursor.next())
  return diags
})

export function HCSP() {
  return new LanguageSupport(HCSPLanguage, [HCSPLinter, annotationPlugin])
}