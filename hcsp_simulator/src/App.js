import './App.css';

import React, {Component} from "react";

import {Nav, Navbar, ButtonToolbar, Button} from "react-bootstrap"
import {FontAwesomeIcon} from '@fortawesome/react-fontawesome'
import {faPlayCircle, faStopCircle, faStepForward, faStepBackward, faPlus} from '@fortawesome/free-solid-svg-icons'
import FlowChart from "./flowChart"


class App extends Component {
    constructor(props) {
        super(props);
        this.changeChart = this.changeChart.bind(this);
    }

    changeChart() {
    }



    render() {
        return (
            <div>
                <Navbar bg="dark" variant="dark">
                    <Navbar.Brand href="#">HCSP Simulator</Navbar.Brand>
                    <Nav className="mr-auto">
                        <Button variant={"primary"}>Read HCSP File</Button>
                    </Nav>
                    <Nav>
                        <Nav.Link href="#features">Readme</Nav.Link>
                        <Nav.Link href="#deets">Contact</Nav.Link>
                    </Nav>
                </Navbar>

                <div>
                    <ButtonToolbar>
                        <Button variant="primary" title={"add hcsp process"} onClick={this.changeChart}><FontAwesomeIcon
                            icon={faPlus} size="lg"/></Button>
                        <Button variant="success" title={"run"}><FontAwesomeIcon icon={faPlayCircle}
                                                                                 size="lg"/></Button>
                        <Button variant="danger" title={"stop"}><FontAwesomeIcon icon={faStopCircle}
                                                                                 size="lg"/></Button>
                        <Button variant="secondary" title={"step forward"}>
                            <FontAwesomeIcon icon={faStepForward} size="lg"/>
                        </Button>
                        <Button variant="secondary" title={"step backward"}>
                            <FontAwesomeIcon icon={faStepBackward} size="lg"/>
                        </Button>
                    </ButtonToolbar>
                </div>
                <FlowChart/>
            </div>
        );
    }
}

export default App;
