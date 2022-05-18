<template>
<span>
  <select class="annotation-button" v-model="ruleSelected" @change="selectRule">
    <option disabled value="" class="annotation-button">Select Verification Rule</option>
    <option v-for="odeRule in odeRules" :key="odeRule" class="annotation-button"> 
      {{ odeRule }}
    </option>
  </select>
  <!-- <select v-model="ruleSelected" class="annotation-button" @change="selectRule">
    <option disabled value="" class="annotation-button">Select Verification Rule</option>
    <option class="annotation-button">Differential Invariant Rule(di)</option>
    <option class="annotation-button">Darboux Rule(dbx)</option>
    <option class="annotation-button">Barrier Certificate Rule(bc)</option>
    <option class="annotation-button">Solution Rule(sln)</option>
  </select> -->
</span>
</template>

<script>
export default {
  name: 'MenuButton',
  props: [],
  data() {
    return {
      odeRules: ["Differential Invariant Rule(di)", "Darboux Rule(dbx)", 
                 "Barrier Certificate Rule(bc)", "Solution Rule(sln)"],
      ruleSelected: ''
    }
  },
  methods: {
    selectRule: function(){
      let startPos = this.ruleSelected.indexOf("(")
      let endPos = this.ruleSelected.indexOf(")")
      this.$emit("selectRule", this.ruleSelected.slice(startPos + 1, endPos))
    }
  }
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
