<template>
<div class="annotation">
  Loop invariant: <input type="text" v-model="loopInv" v-on:input="loopInvChanged">
</div>
</template>

<script>
export default {
  name: 'Annotation',
  props: [],//['ok','condition']
  data: function () {
    return {
      loopInv: ""
    }
  },
  methods : {
    loopInvChanged: function () {
      this.$emit("changed", this.loopInv)
    }
  }
}
</script>

<!-- Add "scoped" attribute to limit CSS to this component only -->
<style scoped>
.annotation {
  border-radius: 20px;
  background: #c6ccbf;
  padding: 0 5px;
  font-family: Avenir, Helvetica, Arial, sans-serif;
}

input {
  font-family: monospace;
  font-size: 20pt;
}
</style>
