<template>
  <div id="app">
    <Editor/>
  </div>
</template>

<script>
import Editor from './components/Editor.vue'

export default {
  name: 'App',
  components: {
    Editor
  }
}
</script>

<style>

html,
body,
#app {
  height: 100%;
  margin: 0;
  font-family: Avenir, Helvetica, Arial, sans-serif;
}
</style>
