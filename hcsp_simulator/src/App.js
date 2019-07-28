import './App.css';

import React, {Component} from "react";

import {Nav, Navbar, ButtonToolbar, Button, Container, Row, Col, Alert} from "react-bootstrap"
import {FontAwesomeIcon} from '@fortawesome/react-fontawesome'
import {faPlayCircle, faStopCircle, faStepForward, faStepBackward} from '@fortawesome/free-solid-svg-icons'
import FlowChart from "./flowChart"
import MonacoEditor from 'react-monaco-editor';


class App extends Component {
    constructor(props) {
        super(props);
        this.state = {
            hcspFileName: undefined,
            hcspCode: "default code...",
            hcspStates: undefined
        };
        this.reader = new FileReader();
    }

    handleFiles = () => {
        console.log(this.fileSelector.files);
        this.reader.onloadend = () => {
            let text = this.reader.result;
            this.setState({hcspCode: text});
        };
        this.reader.readAsText(this.fileSelector.files[0]);
    };


    buildFileSelector = () => {
        const fileSelector = document.createElement('input');
        fileSelector.type = "file";
        fileSelector.onchange = this.handleFiles;
        return fileSelector;
    };

    componentDidMount(): void {
        this.fileSelector = this.buildFileSelector();
    }

    handleFileSelect = (e) => {
        e.preventDefault();
        this.fileSelector.click();
    };



    render() {
        return (
            <div>
                <Navbar bg="light" variant="light">
                    <Navbar.Brand href="#">HCSP Simulator</Navbar.Brand>
                    <Nav className="mr-auto">
                        <Button variant={"primary"} onClick={this.handleFileSelect}>Read HCSP File</Button>
                        {}
                    </Nav>

                    <Nav>
                        <Nav.Link href="#features">Readme</Nav.Link>
                        <Nav.Link href="#deets">Contact</Nav.Link>
                    </Nav>
                </Navbar>

                <div>
                    <ButtonToolbar>
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
                <hr/>
                <Container style={{"maxWidth": window.innerWidth}}>
                    <Row>
                        <Col>
                            <MonacoEditor
                                width={window.innerWidth / 2.2}
                                height={750}
                                language="javascript"
                                theme="vs"
                                value={this.state.hcspCode}
                                options={{
                                    selectOnLineNumbers: true,
                                    minimap: {
                                        enabled: false,
                                    },
                                }}
                            />
                        </Col>
                        <div className="vl"/>
                        <Col><FlowChart hcspState={this.state.hcspStates}/></Col>
                    </Row>
                </Container>

            </div>
        );
    }
}

export default App;
