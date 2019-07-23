import './App.css';

import React, { Component } from "react";

import {Nav, Navbar, ButtonToolbar, Button, Container} from "react-bootstrap"
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faPlayCircle, faStopCircle, faStepForward, faStepBackward, faPlus } from '@fortawesome/free-solid-svg-icons'
import Row from "react-bootstrap/Row";
import Col from "react-bootstrap/Col";

import { FlowChartWithState } from "@mrblenny/react-flow-chart";

class App extends Component {
  render(){
    return (
        <div>
            <Navbar bg="dark" variant="dark">
                <Navbar.Brand href="#">HCSP Simulator</Navbar.Brand>
                <Nav className="mr-auto" >
                    <Button variant={"primary"}>Read HCSP File</Button>
                </Nav>
                <Nav>
                    <Nav.Link href="#features">Readme</Nav.Link>
                    <Nav.Link href="#deets">Contact</Nav.Link>
                </Nav>
            </Navbar>

            <div>
                <ButtonToolbar>
                    <Button variant="primary" title={"add hcsp process"}><FontAwesomeIcon icon={faPlus} size="lg"/></Button>
                    <Button variant="success" title={"run"}><FontAwesomeIcon icon={faPlayCircle} size="lg"/></Button>
                    <Button variant="danger" title={"stop"}><FontAwesomeIcon icon={faStopCircle} size="lg"/></Button>
                    <Button variant="secondary" title={"step forward"}>
                        <FontAwesomeIcon icon={faStepForward} size="lg"/>
                    </Button>
                    <Button variant="secondary" title={"step backward"}>
                        <FontAwesomeIcon icon={faStepBackward} size="lg"/>
                    </Button>
                </ButtonToolbar>
            </div>
            <FlowChartWithState />
        </div>



    );
  }

}

export default App;
