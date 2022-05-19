import {EditorView, Decoration, WidgetType} from "@codemirror/view"
import {StateField, StateEffect} from "@codemirror/state"
import VerificationCondition from "./components/VerificationCondition"
import Vue from "vue"

export class VCWidget extends WidgetType {

    addVCCallback
    vcFormula
  
    constructor(addVCCallback, vcFormula) {
      super();
      this.addVCCallback = addVCCallback;
      this.vcFormula = vcFormula
    }
  
    // eq(other) { } TODO: Need eq method?
  
    toDOM() {
      return new Vue({ 
        ...VerificationCondition,
        propsData: { },
        data: {verifCond: this.vcFormula}
      }).$mount().$on('addAnnotation', this.addVCCallback).$el;
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
    for (let e of tr.effects) if (e.is(addVerificationCondition)) {
      let vcWidget = Decoration.widget({
        widget: new VCWidget(()=>{}, e.value.formula)
      })
      vc = vc.update({
        add: [vcWidget.range(e.value.position, e.value.position)]
      })
    }
    return vc
  },
  provide: f => EditorView.decorations.from(f)
})

export function displayVerificationCondition(view, formula, position) {
    let effects = [addVerificationCondition.of({formula, position})]
      
    if (!view.state.field(verificationConditionField, false))
      effects.push(StateEffect.appendConfig.of([verificationConditionField]))

    view.dispatch({effects})
    return true
  }
  
