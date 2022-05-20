<template>
<span class="annotation-button" >
  {{ vcFormula }}
</span>
</template>

<script>
export default {
  name: 'VerificationCondition',
  props: [],
  data() {
    return {
      vcFormula: ''
    }
  }
}
</script>

<!-- Add "scoped" attribute to limit CSS to this component only -->
<style scoped>
.annotation-button {
  border-radius: 20px;
  background: #1b6a91;
  padding: 0 5px;
  color:white;
  font-weight: bold;
  font-family: Avenir, Helvetica, Arial, sans-serif;
  font-size: smaller;
  cursor: pointer;
}
</style>
