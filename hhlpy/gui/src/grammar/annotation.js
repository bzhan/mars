import {WidgetType,ViewPlugin,Decoration,EditorView} from "@codemirror/view"
import {parser} from "./hcsp_parser"
import {RangeSetBuilder} from "@codemirror/rangeset"
import Annotation from "../components/Annotation"
import AnnotationButton from "../components/AnnotationButton"
import Vue from "vue"
import {StateField, EditorState, EditorSelection, ChangeSet} from "@codemirror/state"

export class AnnotationWidget extends WidgetType {

  changeCallback

  constructor(changeCallback) {
    super();
    this.changeCallback = changeCallback;
  }

  // eq(other) { } TODO: Need eq method?

  toDOM() {
    return new Vue({ 
      ...Annotation,
      propsData: { }
    }).$mount().$on('changed', this.changeCallback).$el;
  }

  ignoreEvent() { return true }
}

export class AnnotationButtonWidget extends WidgetType {

  addAnnotationCallback

  constructor(addAnnotationCallback) {
    super();
    this.addAnnotationCallback = addAnnotationCallback;
  }

  // eq(other) { } TODO: Need eq method?

  toDOM() {
    return new Vue({ 
      ...AnnotationButton,
      propsData: { }
    }).$mount().$on('addAnnotation', this.addAnnotationCallback).$el;
  }

  ignoreEvent() { return true }
}



var marker = "###"
var re = new RegExp("^###.*$","mg");

export const annotationField = StateField.define({
  create() {
    return Decoration.none
  },
  update(annotations, tr) {
    if (!tr.docChanged) return annotations;
    let text = tr.state.doc.toString()
    annotations = [];
    // Find annotation markers and replace them by annotation blocks
    const matches = text.matchAll(re);
    for (const match of matches) {
      var from = match.index;
      var to = from + match[0].length;
      const widget = new AnnotationWidget((val) => {
        console.log(val);
        //TODO: Insert changes into editor
      })
      const annotationDeco = Decoration.replace({widget: widget, block: true})
      annotations.push(annotationDeco.range(from, to));
    }
    return Decoration.set(annotations);
  },
  provide: f => {
    return [
      EditorView.decorations.from(f),
      EditorState.transactionFilter.from(f, (annotations) => {
        return (tr) => {
          let selection;
          // Keep selection out of annotations:
          if (tr.selection) {
            selection = tr.selection;
            let ann = annotations.iter();
            do {
              let from = ann.from;
              let to = ann.to;
              for (let i in selection.ranges) {
                let selRange = selection.ranges[i]
                if (selRange.from >= from && selRange.from < to || selRange.to >= from && selRange.to < to) {
                  selection = selection.replaceRange(EditorSelection.range(to,to), i)
                }
              }
            } while (ann.next())
          }
          // Delete whole block if part is deleted
          let changes = ChangeSet.empty(tr.startState.doc.length);
          tr.changes.iterChanges((fromA, toA, fromB, toB) => {
            let ann = annotations.iter();
            do {
              let from = ann.from;
              let to = ann.to + 1; //Also include the final linebreak
              if (fromB >= from && fromB < to || toB > from && toB <= to) {
                const delAnn = ChangeSet.of({from, to}, tr.startState.doc.length);
                changes = changes.compose(delAnn.map(tr.changes).map(changes));
                selection = EditorSelection.single(from);
              }
            } while (ann.next())
          });
          if (selection)
            return [tr, {changes: changes, selection: selection, sequential: true}]
          else 
            return tr
        }
      })
    ];
  }
})

//TODO: Use viewport / visible ranges to determine where we need to actually do the replacement? 
function addAnnotationButtons(view) {
  let text = view.state.doc.toString()
  // Parse and insert "Add Annotation" buttons after every suitable command
  let builder = new RangeSetBuilder()
  let tree = parser.parse(text)
  let cursor = tree.cursor()
  do {
    if (cursor.name == "RepeatCmd" && text.substr(cursor.to, ("\n" + marker).length) != "\n" + marker) {
      let to = cursor.to
      let deco = Decoration.widget({
        widget: new AnnotationButtonWidget(() => { 
          view.dispatch(view.state.update({changes: {from: to, insert: "\n" + marker + "\n"}}));
        }),
        side: 1
      })
      builder.add(cursor.to,cursor.to,deco)
    }
  } while (cursor.next())
  return builder.finish()
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