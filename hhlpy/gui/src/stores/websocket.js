import { defineStore } from 'pinia'
import Vue from 'vue'

const wsPath = "ws://localhost:8000"

export const useWebsocketStore = defineStore('websocket', {
  state: () => ({ 
    socket: null,
    connected: false,
    listeners: {}
  }),
  actions: {
    reconnect() {
      this.socket = new WebSocket(wsPath)
      this.connected = false
      this.socket.addEventListener("open", () => {
        this.connected = true
      });
      this.socket.addEventListener("close", () => {
        this.connected = false
        setTimeout(() => {
          if (this.socket.readyState !== 1) {
            console.log("Websocket not open. Attempting to reconnect.")
            this.reconnect()
          }
        }, 1000);
      });
      this.socket.addEventListener("message", (event) => {
        let eventData = JSON.parse(event.data)
        if (this.listeners[eventData.type]) {
          for (let i in this.listeners[eventData.type]) {
            this.listeners[eventData.type][i](eventData)
          }
        }
      });
    },

    send(data) {
      if (this.socket.readyState == WebSocket.OPEN) {
        console.log(`WebSocket: Sending ${JSON.stringify(data)}`)
        this.socket.send(JSON.stringify(data))
      } else {
        this.socket.addEventListener("open", () => {
          this.send(data)
        });
      }
    },

    addListener(type, listener) {
      if (!this.listeners[type]) {
        Vue.set(this.listeners, type, [])
      }
      this.listeners[type].push(listener)
    },

    removeListener(type, listener) {
      for (let a in this.listeners[type]) {
        if (listener === this.listeners[type][a]) {
          Vue.delete(this.listeners[type], a)
        }
      }
    }
  },
})
