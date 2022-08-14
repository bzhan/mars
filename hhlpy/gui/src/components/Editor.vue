<template>
  <div :id="'code-' + file" class="code"></div>
</template>

<script>
import {EditorView, basicSetup} from "codemirror"
import { EditorState } from "@codemirror/state"
import {HCSP} from "../grammar/hcsp"
import {indentWithTab} from "@codemirror/commands"
import {keymap} from "@codemirror/view"
import { test_examples } from "../test_examples/examples"
import { originTheme, originField } from '../decoration/origin'

const fixedHeightEditor = EditorView.theme({
  "&": {height: "100%", overflow: "hidden"},
  ".cm-scroller": {overflow: "auto"}
})

export default {
  name: 'Editor',
  props: {
    file: String,
  },
  data: () => { return {
    editorView: null,
  }},
  methods: { 
    initEditor: function (doc) {
      console.log("init editor");
      if (!doc){
        doc = test_examples.e4
      }

      const state = EditorState.create({
        doc: doc,
        extensions: [
          basicSetup,
          keymap.of([indentWithTab]),
          HCSP(),
          originField,
          originTheme,
          fixedHeightEditor,
          // EditorView.lineWrapping,
          EditorView.updateListener.of((v) => {
            if (v.docChanged) {
              this.$emit('docChanged', v.state.doc.toString())
            }
          })
        ]
      })

      this.editorView = new EditorView({
        state: state,
        parent: document.getElementById('code-' + this.file)
      });
      return this.editorView;
    }
  }
}
</script>

<!-- Add "scoped" attribute to limit CSS to this component only -->
<style scoped>
.code {
  overflow: scroll;
  height: 100%;
}
</style>
