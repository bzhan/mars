<template>
<div class="main" ref="main" dropzone="true" ondragover="return false">
    <div class="left" :style="{ width: leftWidth + '%' }"> <slot name="left"></slot> </div>
    <div ref="resizer" class="resizer" draggable="true" @drag="resize"></div>
    <div class="right" :style="{ width: (100 - leftWidth) + '%' }"> <slot name="right"></slot> </div>
</div>
</template>

<script>
export default {
  name: 'Resizer',
  props: {
    initialLeftWidth: Number
  },
  data: () => { return {
    leftWidth: 50,
  }},
  mounted: function () {
    this.leftWidth = this.initialLeftWidth
  },
  methods: { 
    resize(e) {
      if (e.screenX == 0 && e.screenY == 0) {
        return; // Not sure where these events come from
      }
      let container = this.$refs.main
      let min = 10
      this.leftWidth = Math.min(100 - min, Math.max(min, (e.clientX - container.offsetLeft) / container.offsetWidth * 100))
    }
  }
}
</script>

<!-- Add "scoped" attribute to limit CSS to this component only -->
<style scoped>
.main {
  display: flex;
  flex-flow: row;
  height: 100%;
  width: 100%;
  font-size: 120%;
}

.left {
  box-sizing: border-box;
  flex: 1 1 auto;
  overflow: auto;
}
.right {
  box-sizing: border-box;
  flex: 1 1 auto;
  overflow: auto;
}

.resizer {
    width: 5px;
    padding: 0;
    cursor: ew-resize;
    flex: 0 0 auto;
}

.resizer:hover {
  background: lightgray;
}
</style>
