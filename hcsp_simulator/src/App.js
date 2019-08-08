import './App.css';

import React, {Component} from "react";

import {Nav, Navbar, ButtonToolbar, Button, Container} from "react-bootstrap"
import {FontAwesomeIcon} from '@fortawesome/react-fontawesome'
import {faPlayCircle, faStopCircle, faStepForward, faForward, faBackward, faStepBackward} from '@fortawesome/free-solid-svg-icons'
import FlowChart from "./flowChart"
import * as monaco from 'monaco-editor/esm/vs/editor/editor.main.js'
import axios from "axios"


class App extends Component {
    constructor(props) {
        super(props);
        this.state = {
            hcspFileName: undefined,
            hcspCode: "{\n" +
                "\t\"1\": {\n" +
                "\t\t\"code\": \"(<x_dot = 1 & true> |> [](p2c!x --> skip); c2p?x)**\",\n" +
                "\t\t\"state\": {\"x\": 0}\n" +
                "\t},\n" +
                "\t\"2\": {\n" +
                "\t\t\"code\": \"(wait(2); p2c?x; c2p!x-1)**\",\n" +
                "\t\t\"state\": {}\n" +
                "\t},\n" +
                "\t\"3\":{\n" +
                "\t\t\"code\": \"x := x + y; y:= y * x\",\n" +
                "\t\t\"state\": {\"x\":0, \"y\": 1}\n" +
                "\t}\n" +
                "}",
            // hcspStates定义：一个数组序列，每一个元素包含当前代码以及当前状态
            hcspStates: [],
            hcspComm: [],
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
        this.editor = monaco.editor.create(document.getElementById("monaco-editor"), {
            // width: window.innerWidth / 2.2,
            // height: 750,
            theme: "vs",
            value: this.state.hcspCode,
            selectOnLineNumbers: true,
            minimap: {
                enabled: false,
            },

        });
        // this.decorations = this.editor.deltaDecorations([], [{
        //     range: new monaco.Range(7, 1, 7, 24),
        //     options: { inlineClassName: "myInlineDecoration" }
        // }])
    }

    componentDidUpdate(prevProps: Readonly<P>, prevState: Readonly<S>, snapshot: SS): void {
        this.editor.setValue(this.state.hcspCode);
    }

    handleFileSelect = (e) => {
        e.preventDefault();
        this.fileSelector.click();
    };

    run = async (e) => {
        e.preventDefault();
        await this.setStateAsync({hcspCode: this.editor.getValue()});
        try {
            const hcspCode = JSON.parse(this.state.hcspCode);
            this.state.hcspStates.push(hcspCode);
            this.setState({hcspStates: this.state.hcspStates});
        }catch (e) {
            window.alert(e)
        }
        this.setState({started: true})
    };


    forward = async (e) => {
        e.preventDefault();
        const tempCode = this.state.hcspStates[this.state.hcspStates.length - 1];
        const response = await axios.post("/process_multi", tempCode);
        let response_data = response.data;
        console.log("response data:" + JSON.stringify(response_data));
        this.state.hcspStates.push(response_data);
        this.setState({hcspStates: this.state.hcspStates});
    };

    backward = (e) => {
        e.preventDefault();
        if (this.state.hcspStates.length > 1){
            this.setState({hcspState: this.state.hcspStates.pop()});
        }
        console.log(this.state.hcspStates);
    };

    stop = (e) => {
        e.preventDefault();
        this.setState({hcspStates: []});
        this.setState({hcspCode: this.editor.getValue()});
        this.setState({started: false});
        this.editor.deltaDecorations(this.decorations, []);
    };


    nextStep = async (e) => {
        e.preventDefault();
        const tempCode = this.state.hcspStates[this.state.hcspStates.length - 1]['code'];
        const input = this.state.hcspStates[this.state.hcspStates.length - 1]['state'];
        const reason = this.state.hcspStates[this.state.hcspStates.length - 1]['reason'];
        const response = await axios.post("/step", {"code": tempCode, "input": input, "reason": reason});
        let response_data = response.data;
        const new_code = response_data['new_code'];
        const new_state = response_data['new_state'];
        const new_reason = response_data['reason'];
        this.state.hcspStates.push(
            {
                "code": new_code,
                "state": new_state,
                "reason": new_reason
            }
        );
        this.setState({hcspStates: this.state.hcspStates});
    };

    lastStep = (e) => {
        e.preventDefault();
    };


    setStateAsync = (state) => {
        return new Promise((resolve) => {
            this.setState(state, resolve)
        });
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
                        <Button variant="success" title={"run"} onClick={this.run} disabled={this.state.started}><FontAwesomeIcon icon={faPlayCircle}
                                                                                 size="lg"/></Button>

                        <Button variant="danger" title={"stop"} onClick={this.stop} disabled={!this.state.started}><FontAwesomeIcon icon={faStopCircle}
                                                                                 size="lg"/></Button>
                        <Button variant="secondary" title={"step forward"} onClick={this.nextStep} disabled={!this.state.started}>
                            <FontAwesomeIcon icon={faForward} size="lg"/>
                        </Button>
                        <Button variant="secondary" title={"step backward"} onClick={this.lastStep} disabled={!this.state.started}>
                            <FontAwesomeIcon icon={faBackward} size="lg"/>
                        </Button>
                        <Button variant="secondary" title={"forward"} onClick={this.forward} disabled={!this.state.started}><FontAwesomeIcon icon={faStepForward}
                                                                                                                                             size="lg"/></Button>
                        <Button variant="secondary" title={"backward"} onClick={this.backward} disabled={!this.state.started}><FontAwesomeIcon icon={faStepBackward}
                                                                                                                                             size="lg"/></Button>
                    </ButtonToolbar>
                </div>
                <hr/>
                <Container style={{"maxWidth": window.innerWidth}}>
                    <div id="monaco-editor" style={{height: 250}}/>
                    <hr/>
                    <FlowChart style={{"maxWidth": window.innerWidth}} hcspStates={this.state.hcspStates}/>
                </Container>
            </div>
        );
    }
}

export default App;
