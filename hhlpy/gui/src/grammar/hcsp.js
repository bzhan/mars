import {parser} from "./hcsp_parser"
import {LRLanguage, LanguageSupport, indentNodeProp, foldNodeProp, foldInside, continuedIndent} from "@codemirror/language"
import {styleTags, tags as t} from "@codemirror/highlight"
import {completeFromList} from "@codemirror/autocomplete"
import {snippets} from "./snippets"

export const HCSPLanguage = LRLanguage.define({
  parser: parser.configure({
    props: [
      indentNodeProp.add({
        WaitCmd: continuedIndent({except:/\)/}),
        AssignCmd: continuedIndent(),
        MultiAssignCmd: continuedIndent(),
        RandomAssignCmd: continuedIndent({except:/\}/}),
        AssertCmd: continuedIndent({except:/\)/}),
        TestCmd: continuedIndent({except:/\)/}),
        LogCmd: continuedIndent({except:/\)/}),
        RepeatCmd: continuedIndent({except:/\)\*\*/}),
        RepeatCondCmd: continuedIndent({except:/(\)\{|\}\*\*)/}),
        RepeatCmdInv: continuedIndent({except:/(\)\*\*@invariant\(|\))/}),
        RepeatCondCmdInv: continuedIndent(),
        Ode: continuedIndent({except:/>/}),
        OdeCommConst: continuedIndent({except:/(>|\))/}),
        OdeComm: continuedIndent({except:/(>|\))/}),
        RecCmd: continuedIndent({except:/\)/}),
        IteCmd: continuedIndent({except:/(if|then|else|elif|endif)/}),
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
        "if then else elif endif rec log test assert": t.controlKeyword,
        "+ - %": t.operator,
        "|| && -->": t.logicOperator,
        "> >= < <=" : t.compareOperator,
        "min max gcd" : t.operatorKeyword,
        "skip wait assert test log" : t.keyword
      })
    ]
  }),
  languageData: {
    commentTokens: {line: "#"},
    indentOnInput: /^\s*(\}|then|else|elif|endif|\)|>)$/
  }
})

export const HCSPCompletion = HCSPLanguage.data.of({
  autocomplete: completeFromList(snippets)
})

export function HCSP() {
  return new LanguageSupport(HCSPLanguage, [HCSPCompletion])
}