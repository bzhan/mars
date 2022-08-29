
const wsPath = "ws://localhost:8000"

class ServerConnection {
  constructor() {
    const openConnection = () => {
      this.socket = new WebSocket(wsPath);
    
      this.socket.addEventListener("open", () => {
        
      });
    
      this.socket.addEventListener("message", () => {
        // let eventData = JSON.parse(event.data)
        // console.log(event)
      }); 
    }
    
    openConnection();
    
    // Regularly check if connection is still open. Otherwise, reconnect.
    setInterval(() => {
      if (this.socket.readyState !== 1) {
        console.log("Websocket not open. Attempting to reconnect.")
        openConnection();
      }
    }, 5000);
  }
  
}



export const serverConnection = new ServerConnection();