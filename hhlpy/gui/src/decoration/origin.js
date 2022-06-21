import {EditorView, Decoration} from "@codemirror/view"
import {StateField, StateEffect} from "@codemirror/state"

export const showOrigin = StateEffect.define()
export const hideOrigin = StateEffect.define()

export const originField = StateField.define({
  create() {
    return Decoration.none
  },
  update(originSet, tr) {
    if (tr.docChanged || tr.effects.some(e => e.is(showOrigin) || e.is(hideOrigin))) {
        originSet = Decoration.none
    }
    for (let e of tr.effects) {
        if (e.is(showOrigin)) {
            originSet = originSet.update({
                add: [originMark.range(e.value.from, e.value.to)]
            })
        }
    }
    return originSet
  },
  provide: f => EditorView.decorations.from(f)
})

const originMark = Decoration.mark({class: "cm-origin"})

export const originTheme = EditorView.baseTheme({
".cm-origin": { backgroundColor: "rgba(255, 150, 0, 0.4);" }
})