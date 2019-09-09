import './App.css';

import React from "react";

import {Nav, Navbar, ButtonToolbar, Button, Container} from "react-bootstrap"
import {FontAwesomeIcon} from '@fortawesome/react-fontawesome'
import {faPlayCircle, faSync, faCaretRight, faForward, faBackward, faCaretLeft} from '@fortawesome/free-solid-svg-icons'
import axios from "axios"


class Process extends React.Component {
    render() {
        return (
            <div>
            <div className="program-text">
                {this.props.lines.map((str, line_no) => {
                    if (this.props.start === undefined) {
                        return <pre key={line_no}>{str}</pre>
                    }
                    var bg_start, bg_end;
                    const sl = this.props.start[0];
                    const sc = this.props.start[1];
                    const el = this.props.end[0];
                    const ec = this.props.end[1];
                    if (line_no === sl) {
                        bg_start = sc;
                    } else if (line_no > sl) {
                        bg_start = 0;
                    } else {
                        bg_start = str.length;
                    }
                    if (line_no === el) {
                        bg_end = ec;
                    } else if (line_no < el) {
                        bg_end = str.length;
                    } else {
                        bg_end = 0;
                    }
                    if (bg_start < bg_end) {
                        return (
                            <pre key={line_no}>
                                <span>{str.slice(0,bg_start)}</span>
                                <span className="program-text-hl">{str.slice(bg_start,bg_end)}</span>
                                <span>{str.slice(bg_end,str.length)}</span>
                            </pre>)
                    }
                    return <pre key={line_no}>{str}</pre>
                })}
            </div>
            <pre className="program-state">
                <span>&nbsp;</span>
                {this.props.state.map((pair, index) => {
                    const var_name = pair[0];
                    const val = pair[1];
                    return <span key={index} style={{marginLeft: "10px"}}>{var_name}: {val}</span>
                })}
            </pre>
            </div>
        );
    }
}

class Events extends React.Component {
    render() {
        return (
            <div className="event-list">
                {this.props.events.map((event, index) => {
                    if (index === this.props.current_index) {
                        return <pre key={index}><span className="event-list-hl">{event}</span></pre>
                    } else {
                        return <pre key={index}>{event}</pre>
                    }
                })}
            </div>
        )
    }
}

class App extends React.Component {
    constructor(props) {
        super(props);
        this.state = {
            // Name of the currently open file
            hcspFileName: "",

            // Code for the HCSP program, one entry for each process 
            hcspCode: [],

            // Pretty-printed form of the HCSP program
            print_info: [],

            // Currently computed history. Each entry represents one
            // state in the execution. The first entry is the starting
            // state. All other entries are waiting for some event.
            // Each entry contains the position and state of the program
            // at each step.
            history: [],

            // List of events. The events[i] carries history[i+1] to
            // history[i+2].
            events: [],

            // Current position
            history_pos: 0,

            // Whether there is a file loaded.
            file_loaded: false
        };
        this.reader = new FileReader();
        this.fileSelector = undefined;
    }

    handleFiles = () => {
        this.reader.onloadend = async () => {
            let text = this.reader.result;
            let hcspCode = text.trim().split('\n');
            const response = await axios.post("/parse_hcsp", {
                hcspCode: hcspCode,
            })
            console.log(response);
            this.setState({
                hcspCode: hcspCode,
                print_info: response.data.print_info,
                hcspFileName: this.fileSelector.files[0].name,
                file_loaded: true,
                history: [],
                events: [],
                history_pos: 0,
            });
        };
        this.reader.readAsText(this.fileSelector.files[0]);
    };


    buildFileSelector = () => {
        const fileSelector = document.createElement('input');
        fileSelector.type = "file";
        fileSelector.onchange = this.handleFiles;
        return fileSelector;
    };

    componentDidMount() {
        this.fileSelector = this.buildFileSelector();
    }

    handleFileSelect = (e) => {
        e.preventDefault();
        this.fileSelector.value = "";
        this.fileSelector.click();
    };

    run = async (e) => {
        e.preventDefault();
        const response = await axios.post("/run_hcsp", {
            hcspCode: this.state.hcspCode,
            num_steps: 100,
        })
        this.setState({
            history: response.data.history,
            events: response.data.events,
        })
    };

    nextEvent = (e) => {
        this.setState((state) => ({
            history_pos: state.history_pos + 1
        }))
    };

    prevEvent = (e) => {
        this.setState((state) => ({
            history_pos: state.history_pos - 1
        }))
    };

    nextStep = (e) => {
    };

    prevStep = (e) => {
    };

    setStateAsync = (state) => {
        return new Promise((resolve) => {
            this.setState(state, resolve);
        });
    };


    render() {
        return (
            <div>
                <Navbar bg="light" variant="light">
                    <Navbar.Brand href="#">HCSP Simulator</Navbar.Brand>
                    <Nav className="mr-auto">
                        <Button variant={"primary"} onClick={this.handleFileSelect}>Read HCSP File</Button>
                        <span style={{marginLeft: '20px', fontSize: 'x-large'}}>{this.state.hcspFileName}</span>
                    </Nav>
                </Navbar>

                <div>
                    <ButtonToolbar>
                        <Button variant="success" title={"run"} onClick={this.run} disabled={!this.state.file_loaded}>
                            <FontAwesomeIcon icon={faPlayCircle} size="lg"/>
                        </Button>

                        <Button variant="secondary" title={"refresh"} onClick={this.handleFiles} disabled={!this.state.file_loaded}>
                            <FontAwesomeIcon icon={faSync} size="lg"/>
                        </Button>

                        <Button variant="secondary" title={"step forward"} onClick={this.nextEvent}
                            disabled={this.state.history.length === 0 || this.state.history_pos === this.state.history.length-1}>
                            <FontAwesomeIcon icon={faForward} size="lg"/>
                        </Button>

                        <Button variant="secondary" title={"step backward"} onClick={this.prevEvent}
                            disabled={this.state.history.length === 0 || this.state.history_pos === 0}>
                            <FontAwesomeIcon icon={faBackward} size="lg"/>
                        </Button>

                        <Button variant="secondary" title={"forward"} onClick={this.nextStep} disabled={!this.state.started}>
                            <FontAwesomeIcon icon={faCaretRight} size="lg"/>
                        </Button>

                        <Button variant="secondary" title={"backward"} onClick={this.prevStep} disabled={!this.state.started}>
                            <FontAwesomeIcon icon={faCaretLeft} size="lg"/>
                        </Button>
                    </ButtonToolbar>
                </div>

                <hr/>
                <Container className="left">
                    {this.state.print_info.map((info, index) => {
                        const lines = info[0];
                        const mapping = info[1];
                        if (this.state.history.length === 0) {
                            return <Process key={index}
                                lines={lines} start={undefined} end={undefined} state={[]}/>
                        } else {
                            const hpos = this.state.history_pos;
                            const pos = this.state.history[hpos][index].pos;
                            const start = mapping[pos][0];
                            const end = mapping[pos][1];
                            const state = this.state.history[hpos][index].state;
                            return <Process key={index}
                                lines={lines} start={start} end={end} state={state}/>    
                        }
                    })}
                </Container>
                <Container className="right">
                    <Events events={this.state.events} current_index={this.state.history_pos}/>
                </Container>
            </div>
        );
    }
}

export default App;
