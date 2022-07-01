// import {EditorView, Panel} from "@codemirror/view"
// import {Text} from "@codemirror/state"
import {showPanel} from "@codemirror/panel"
// import VerificationCondition from "../components/VerificationCondition"
// import Vue from "vue"

function countWords(doc) {
  let count = 0, iter = doc.iter()
  while (!iter.next().done) {
    let inWord = false
    for (let i = 0; i < iter.value.length; i++) {
      let word = /\w/.test(iter.value[i])
      if (word && !inWord) count++
      inWord = word
    }
  }
  return `Word count: ${count}`
}

function wordCountPanel(view) {
  let dom = document.createElement("div")
  dom.textContent = countWords(view.state.doc)
  return {
    dom,
    update(update) {
      if (update.docChanged)
        dom.textContent = countWords(update.state.doc)
    }
  }
}

// function verificationCondition(view, changeSolverCallback, vcFormula, vcSolver, vcResult, vcOrigin) {
//   let vcComp = new Vue({ 
//     ...VerificationCondition,
//     propsData: {
//       view: view
//     },
//     data: {
//       vcFormula: vcFormula,
//       vcSolver: vcSolver,
//       vcResult: vcResult,
//       vcOrigin: vcOrigin
//     }
//   })
//   .$mount()
//   .$on("changeSolver", changeSolverCallback)
//   .$el;

//   return {
//     vcComp
//   }
// }

export function wordCounter() {
  return showPanel.of(wordCountPanel)
}