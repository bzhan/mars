import {WidgetType,ViewPlugin,Decoration} from "@codemirror/view"
import {parser} from "../grammar/hcsp_parser"
import {RangeSetBuilder} from "@codemirror/state"
import AnnotationButton from "../components/AnnotationButton"
import MenuButton from "../components/MenuButton"
import Vue from "vue"

export class AnnotationButtonWidget extends WidgetType {

  addAnnotationCallback
  annotationName

  constructor(addAnnotationCallback, annotationName) {
    super();
    this.addAnnotationCallback = addAnnotationCallback;
    this.annotationName = annotationName
  }

  // eq(other) { } TODO: Need eq method?

  toDOM() {
    return new Vue({ 
      ...AnnotationButton,
      propsData: { },
      data: {buttonName: this.annotationName}
    }).$mount().$on('addAnnotation', this.addAnnotationCallback).$el;
  }

  ignoreEvent() { return true }
}

export class MenuButtonWidget extends WidgetType {

  selectRuleCallback

  constructor(selectRuleCallback) {
    super();
    this.selectRuleCallback = selectRuleCallback;
  }

  // eq(other) { } TODO: Need eq method?

  toDOM() {
    return new Vue({ 
      ...MenuButton,
      propsData: { }
    }).$mount().$on('selectRule', this.selectRuleCallback).$el;
  }

  ignoreEvent() { return true }
}


//TODO: Use viewport / visible ranges to determine where we need to actually do the replacement? 
function addAnnotationButtons(view) {
  let text = view.state.doc.toString()
  // Parse and insert "Add Annotation" buttons after every suitable command
  let builder = new RangeSetBuilder()
  let tree = parser.parse(text)
  let cursor = tree.cursor()

  let inv_desc = "invariant "
  let inv_desc_len = inv_desc.length
  let space_len = 4
  let ghost_desc = "ghost "
  let ghost_desc_len = ghost_desc.length

  // Iterate over the root node and all its descendants
  cursor.iterate(
    () => {}, // Do nothing when entering the node.
    (cursor) => { // Add annotation buttons when leaving the node.
    let to = cursor.to

    if (cursor.name == "RepeatCmd") {
      // RepeatCmd: "{" cmd "}" "*" ("invariant" Loop_invariant+ ";")?
      let inv_changes = {}
      let inv_selection = {}

      // Add key word "invariant" if it's a RepeatCmd without invariant.
      if (cursor.node.lastChild.name == "*") {
        inv_changes = {from: to, insert: "\n\t" + inv_desc + "[" + " ".repeat(space_len) + "];"}
        inv_selection = {anchor: to + inv_desc_len + 3, head: to + inv_desc_len + 3 + space_len}
      }
      // Add "[    ]" before ";" otherwise.
      else {
        inv_changes = {from: to-1, 
                       insert: "\n\t" + " ".repeat(inv_desc_len) + 
                                "[" + " ".repeat(space_len) + "]"}
        inv_selection = {anchor: to-1 + inv_desc_len + 3, 
                          head: to-1 + inv_desc_len + 3 + space_len}
      }

      let deco = Decoration.widget({
        widget: new AnnotationButtonWidget(() => { 
          view.dispatch(view.state.update({
            changes: inv_changes, 
            selection: inv_selection}))
        },
        "Add Invariant"),
        side: 1
      })
      // Place the button after { cmd }*, i.e. after the forth child.
      builder.add(cursor.node.firstChild.nextSibling.nextSibling.nextSibling.to, 
                  cursor.node.firstChild.nextSibling.nextSibling.nextSibling.to, 
                  deco)
    }

    // Ode: OdeNoInv ("invariant" Ode_invariant+ ";")?
    else if (cursor.name == "OdeNoInv") {
      // OdeNoInv: "{" ode_seq "&" expr "}" 
      if (!includeError(cursor.node)){
        // Button for adding invariant and ghostfor ODE.
        let inv_changes = {}
        let inv_selection = {}
        let ghost_changes = {}
        let ghost_selection = {}
        
        // Add keyword "invariant" when OdeNoInv is the only child of node Ode.
        if (!cursor.node.nextSibling){  
          inv_changes = {from: to, 
                         insert: "\n\t" + inv_desc + "[" + " ".repeat(space_len) + "];"} 
          inv_selection = {anchor: to + inv_desc_len + 3, 
                           head: to + inv_desc_len + 3 + space_len}
          ghost_changes = {from: to, 
                           insert: "\n\t" + inv_desc + ghost_desc} 
          ghost_selection = {anchor: to + inv_desc_len + ghost_desc_len + 2}    
        }

        // Do not need "invariant " description if there is already one invariant above.
        else{
          // Add "[    ]" before ";"
          // node.parent is Ode: OdeNoInv ("invariant" Ode_invariant+ ";")?
          let from = cursor.node.parent.lastChild.from
          inv_changes = {from: from, 
                         insert: "\n\t" + " ".repeat(inv_desc_len) + 
                                     "[" + " ".repeat(space_len) + "]"}
          inv_selection = {anchor: from + inv_desc_len + 3, 
                       head: from + inv_desc_len + 3 + space_len}
          ghost_changes = {from: from, 
                           insert: "\n\t" + " ".repeat(inv_desc_len) + ghost_desc}
          ghost_selection = {anchor: from + inv_desc_len + ghost_desc_len + 2}
        }

        let inv_deco = Decoration.widget({
          widget: new AnnotationButtonWidget(
            () => {
              view.dispatch(view.state.update({
                changes: inv_changes,
                selection: inv_selection
              }))
              },
            "Add Invariant"),
          side: 2    
        })

        // Button for adding ghost for ODE.
        let ghost_deco = Decoration.widget({
          widget: new AnnotationButtonWidget(
            () => {
              view.dispatch(view.state.update({
                changes: ghost_changes,
                selection: ghost_selection
              }))
              },
            "Add Ghost"),
          side: 3
        })

        let sln_deco = Decoration.widget({
          widget: new AnnotationButtonWidget(
            () => {
                view.dispatch(view.state.update({
                    changes: {from: to, insert: "\n\tsolution;"},
                    selection: {anchor: to + "\n\tsolution;".length}
                }))
            },
            "Solve"),
          side: 1
        })
        
        builder.add(cursor.node.to, cursor.node.to, sln_deco)
        builder.add(cursor.node.to, cursor.node.to, inv_deco)
        builder.add(cursor.node.to, cursor.node.to, ghost_deco)
      }
    }

    else if (cursor.name == "InvariantWithRule"){
      // InvariantWithRule: Invariant ("{" ode_rule "}")? 

      // The rule inserted starts from the end of Invariant(firstChild).
      let ruleFrom = cursor.node.firstChild.to

      let deco = Decoration.widget({
        widget: new MenuButtonWidget(
          (odeRule) => {
            view.dispatch(view.state.update({
              changes: {from: ruleFrom, to: to, insert: "{" + odeRule + "}"}
            }))
          }
        )
      })
      builder.add(cursor.to, cursor.to, deco)
    }
  }
)
  return builder.finish()
}

/** Check whether the sub-tree of the node includes errors.
 * Return true if it includes errors.
 * Return false if the node sub-tree is completely correct.*/ 
function includeError(node){
  // let cursor = node.cursor
  // do {
  //   if (cursor.type.isError) {
  //     return true
  //   }
  // }while(cursor.next())

  if (node.type.isError){
    return true
  }

  return false
}

export const annotationPlugin = ViewPlugin.fromClass(class {
  decorations

  constructor(view) {
    this.decorations = addAnnotationButtons(view)
  }

  update(update) {
    //TODO: Maybe run together with linter? (So we don't slow down anything and we don't need to reparse)
    if (update.docChanged)
      this.decorations = addAnnotationButtons(update.view)
  }
}, {
  decorations: v => v.decorations,
  eventHandlers: {
    mousedown: (e, view) => {
      console.log(e)
      console.log(view.posAtDOM(e.target))
    }
  }
})