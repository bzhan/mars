<template>
<span>
  <!-- <span class="annotation-button" v-on:click="openMenu">
    {{ buttonName }}
  </span> -->
  <select name="ruleSelected" class="annotation-button" v-model="ruleSelected" @change="selectRule">
    <option v-for="odeRule in odeRules" :key="odeRule" class="annotation-button" :value="odeRule"> 
      {{ odeRule }}
    </option>
  </select>
</span>
</template>

<script>
export default {
  name: 'MenuButton',
  props: [],
  data() {
    return {
      buttonName: 'Select Verification Rule',
      odeRules: ["Differential Invariant Rule(di)", "Darboux Rule(dbx)", 
                 "Barrier Certificate Rule(bc)", "Solution Rule(sln)"],
      ruleSelected: "Differential Invariant Rule(di)"
      // menuOpen: false
    }
  },
  methods: {
    selectRule: function () {
      let startPos = this.ruleSelected.indexOf("(")
      let endPos = this.ruleSelected.indexOf(")")
      this.$emit("selectRule", this.ruleSelected.slice(startPos + 1, endPos))
    },
    // openMenu: function(){
    //   this.menuOpen = true
    // },
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
