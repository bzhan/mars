<template>
<span>
    <label for="z3">
      <input type="radio" id="z3" value="z3" v-model="vcSolver">Z3
    </label>
    <label for="wol">
      <input type="radio" id="wol" value="wolfram_engine" v-model="vcSolver">Wolfram Engine
    </label>
</span>
</template>

<script>
export default {
  name: 'solverSelect',
  props: [],
  data() {
    return {
      vcSolver: 'z3'
    }
  },
  computed:{
    z3() {
      if (this.solver === "z3")
        return true
      else
        return false
    },
    wolfram_engine() {
      if (this.solver === "wolfram_engine")
        return true
      else
        return false
    }
  },
}
</script>

<!-- Add "scoped" attribute to limit CSS to this component only -->
<style scoped>
.annotation-button {
  border-radius: 20px;
  background: #60911b;
  padding: 0 5px;
  color:white;
  font-weight: bold;
  font-family: Avenir, Helvetica, Arial, sans-serif;
  font-size: smaller;
  cursor: pointer;
}
</style>
