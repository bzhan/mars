<template>
<span class="annotation-button" >
  {{ verifCond }}
</span>
</template>

<script>
export default {
  name: 'VerificationCondition',
  props: [],
  data() {
    return {
      verifCond: ''
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
