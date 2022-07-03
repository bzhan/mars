import {WidgetType,ViewPlugin,Decoration} from "@codemirror/view"
import {parser} from "../grammar/hcsp_parser"
import {RangeSetBuilder} from "@codemirror/rangeset"
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

  do {
    let to = cursor.to

    if (cursor.name == "RepeatCmd") {
      let inv_changes = {}
      let inv_selection = {}
      console.log("cursor name:", cursor.name)
      console.log("last child name:", cursor.node.lastChild.cursor.name)
      if (cursor.node.lastChild.cursor.name != ";") {
        inv_changes = {from: to, insert: "\n\t" + inv_desc + "[" + " ".repeat(space_len) + "];"}
        inv_selection = {anchor: to + inv_desc_len + 3, head: to + inv_desc_len + 3 + space_len}
      }
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
      builder.add(cursor.node.firstChild.nextSibling.nextSibling.nextSibling.cursor.to, 
                  cursor.node.firstChild.nextSibling.nextSibling.nextSibling.cursor.to, 
                  deco)
    }

    else if (cursor.name == "Ode") {
      if (!includeError(cursor.node)){
        // Button for adding invariant for ODE.
        // Insert "invariant " description when no ode_invariant is injected before.
        let inv_changes = {}
        let inv_selection = {}
        let ghost_changes = {}
        let ghost_selection = {}
        if (cursor.node.lastChild.cursor.name != ";"){  
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
          inv_changes = {from: to-1, 
                         insert: "\n\t" + " ".repeat(inv_desc_len) + 
                                     "[" + " ".repeat(space_len) + "]"}
          inv_selection = {anchor: to-1 + inv_desc_len + 3, 
                       head: to-1 + inv_desc_len + 3 + space_len}
          ghost_changes = {from: to-1, 
                           insert: "\n\t" + " ".repeat(inv_desc_len) + ghost_desc}
          ghost_selection = {anchor: to-1 + inv_desc_len + ghost_desc_len + 2}
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
          side: 1    
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
          side: 2
        })
        builder.add(cursor.node.firstChild.cursor.to, cursor.node.firstChild.cursor.to, inv_deco)
        builder.add(cursor.node.firstChild.cursor.to, cursor.node.firstChild.cursor.to, ghost_deco)
      }
    }

    else if (cursor.name == "InvariantWithRule"){
      // Grammar: InvariantWithRule { Invariant ("{" ode_rule "}")? }
      let ruleFrom = to

      // When the node is already with a selected rule, if we want to change the rule, 
      // we need to replace the old rule with the new one.
      if (cursor.node.lastChild.cursor.name == "}") {
        // Position of the new rule starts at the end of Invariant(firstChild)
        ruleFrom = cursor.node.firstChild.cursor.to
      }
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
  } while (cursor.next())
  return builder.finish()
}

/** Check whether the sub-tree of the node includes errors.
 * Return true if it includes errors.
 * Return false if the node sub-tree is completely correct.*/ 
function includeError(node){
  let cursor = node.cursor
  do {
    if (cursor.type.isError) {
      return true
    }
  }while(cursor.next())

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