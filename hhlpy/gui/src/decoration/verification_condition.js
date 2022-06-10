import {EditorView, Decoration, WidgetType} from "@codemirror/view"
import {StateField, StateEffect} from "@codemirror/state"
import VerificationCondition from "../components/VerificationCondition"
import Vue from "vue"

export class VCWidget extends WidgetType {

    changeSolverCallback
    vcFormula
    vcSolver
    vcResult
  
    constructor(changeSolverCallback, vcFormula, vcSolver, vcResult) {
      super();
      this.changeSolverCallback = changeSolverCallback;
      this.vcFormula = vcFormula
      this.vcSolver = vcSolver
      this.vcResult = vcResult
    }
  
    // eq(other) { } TODO: Need eq method?
  
    toDOM() {
      return new Vue({ 
        ...VerificationCondition,
        propsData: { },
        data: {
          vcFormula: this.vcFormula,
          vcSolver: this.vcSolver,
          vcResult: this.vcResult
        }
      }).$mount().$on("changeSolver", this.changeSolverCallback).$el;
    }
  
    ignoreEvent() { return true }
  }

const addVerificationCondition = StateEffect.define()

const verificationConditionField = StateField.define({
  create() {
    return Decoration.none
  },
  update(vc, tr) {
    vc = vc.map(tr.changes)
    for (let e of tr.effects) {
      if (e.is(addVerificationCondition)) {
        let vcWidget = Decoration.widget({
          widget: new VCWidget(
              e.value.changeSolverCallback, 
              e.value.formula, 
              e.value.solver,
              e.value.result),
          block: true,
          side: 1
        })
        vc = vc.update({
          add: [vcWidget.range(e.value.position, e.value.position)]
        })
      }
      else if (e.is(clearVerificationCondition)) {
        vc = Decoration.none
      }
    }
    return vc
  },
  provide: f => EditorView.decorations.from(f)
})

export function displayVerificationCondition(view, formula, position, changeSolverCallback, solver, result) {
    let effects = [addVerificationCondition.of({formula, position, changeSolverCallback, solver, result})]
      
    if (!view.state.field(verificationConditionField, false))
      effects.push(StateEffect.appendConfig.of([verificationConditionField]))
    
    view.dispatch({effects})
  
    return true
  }

/**Get postion for a given line */
export function getPosition(view, lineNumber) {
   return view.state.doc.line(lineNumber).to
}

const clearVerificationCondition = StateEffect.define()

export function removeVerificationCondition(view){
  let effects = [clearVerificationCondition.of({})]
      
  if (!view.state.field(verificationConditionField, false))
    effects.push(StateEffect.appendConfig.of([verificationConditionField]))
  
  view.dispatch({effects})

  return true
}

