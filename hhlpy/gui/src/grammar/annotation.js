import {WidgetType,ViewPlugin,Decoration} from "@codemirror/view"
import {parser} from "./hcsp_parser"
import {RangeSetBuilder} from "@codemirror/rangeset"
import Annotation from "../components/Annotation"
import Vue from "vue"

export class AnnotationWidget extends WidgetType {

  // eq(other) { } TODO: Need eq method?

  toDOM() {
    return new Vue({ 
      ...Annotation,
      propsData: { }
    }).$mount().$el;
  }

  ignoreEvent() { return false }
}

function addAnnoations(view) {
  let tree = parser.parse(view.state.doc.toString())
  let cursor = tree.cursor()
  let builder = new RangeSetBuilder()
  do {
    if (cursor.name == "RepeatCmd") {
      let deco = Decoration.widget({
        widget: new AnnotationWidget(true),
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
    this.decorations = addAnnoations(view)
  }

  update(update) {
    if (update.docChanged)
      this.decorations = addAnnoations(update.view)
  }
}, {
  decorations: v => v.decorations
})