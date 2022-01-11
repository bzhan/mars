import {parser} from "./hcsp_parser"
import {LRLanguage, LanguageSupport, indentNodeProp, foldNodeProp, foldInside, delimitedIndent} from "@codemirror/language"
import {styleTags, tags as t} from "@codemirror/highlight"

export const HCSPLanguage = LRLanguage.define({
  parser: parser.configure({
    props: [
      indentNodeProp.add({
        Application: delimitedIndent({closing: ")", align: false})
      }),
      foldNodeProp.add({
        Application: foldInside
      }),
      styleTags({
        CNAME: t.variableName,
        LineComment: t.lineComment,
        ESCAPED_STRING: t.string,
        SIGNED_NUMBER: t.number,
        "( )": t.paren,
        "if then else elif endif": t.controlKeyword,
      })
    ]
  }),
  languageData: {
    commentTokens: {line: "#"}
  }
})

export function HCSP() {
  return new LanguageSupport(HCSPLanguage)
}