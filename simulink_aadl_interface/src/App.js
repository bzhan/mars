import './App.css';

import React, {Component} from "react";

import {Nav, Navbar, ButtonToolbar, Button, Container} from "react-bootstrap"
import {FontAwesomeIcon} from '@fortawesome/react-fontawesome'
import {faPlayCircle, faStopCircle, faStepForward, faForward, faBackward, faStepBackward} from '@fortawesome/free-solid-svg-icons'

import * as monaco from 'monaco-editor/esm/vs/editor/editor.main.js'
import axios from "axios"


class App extends Component {
    constructor(props) {
        super(props);
        this.state = {
            started: false
        };
        this.reader = new FileReader();
    }

    handleFiles = () => {
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

    componentDidUpdate(prevProps: Readonly<P>, prevState: Readonly<S>, snapshot: SS): void {
        this.editor.setValue(this.state.hcspCode);
    }

    handleFileSelect = (e) => {
        e.preventDefault();
        this.fileSelector.click();
    };


    render() {
        return (
            <div>
                <Navbar bg="light" variant="light">
                    <Navbar.Brand href="#">Simulink AADL Interface</Navbar.Brand>
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
                        <Button variant="success" title={"run"} disabled={this.state.started}><FontAwesomeIcon icon={faPlayCircle}
                                                                                 size="lg"/></Button>

                        <Button variant="danger" title={"stop"} disabled={!this.state.started}><FontAwesomeIcon icon={faStopCircle}
                                                                                 size="lg"/></Button>
                        <Button variant="secondary" title={"step forward"} disabled={!this.state.started}>
                            <FontAwesomeIcon icon={faForward} size="lg"/>
                        </Button>
                        <Button variant="secondary" title={"step backward"} disabled={!this.state.started}>
                            <FontAwesomeIcon icon={faBackward} size="lg"/>
                        </Button>
                        <Button variant="secondary" title={"forward"} disabled={!this.state.started}><FontAwesomeIcon icon={faStepForward} size="lg"/></Button>
                        <Button variant="secondary" title={"backward"} disabled={!this.state.started}><FontAwesomeIcon icon={faStepBackward} size="lg"/></Button>
                    </ButtonToolbar>
                </div>
                <hr/>
            </div>
        );
    }
}

export default App;
