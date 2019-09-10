import './App.css';

import React from "react";

import {Nav, Navbar, ButtonToolbar, Button, Container} from "react-bootstrap"
import {FontAwesomeIcon} from '@fortawesome/react-fontawesome'
import {faPlayCircle, faSync, faCaretRight, faForward, faBackward, faCaretLeft} from '@fortawesome/free-solid-svg-icons'
import {Chart} from 'chart.js'
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
            {this.props.time_series !== undefined ?
                <canvas id={'chart'+String(this.props.index)} width="400" height="100"/> : null
            }
            </div>
        );
    }

    componentDidUpdate() {
        const ts = this.props.time_series;
        if (ts === undefined) {
            return;
        }
        var series = {};
        for (let i = 0; i < ts.length; i++) {
            for (let k in ts[i].state) {
                if (!(k in series)) {
                    series[k] = [];
                }
                series[k].push({x: ts[i].time, y: ts[i].state[k]});
            }
        }
        var datasets = [];
        var colors = ['blue', 'red', 'green', 'yellow'];
        for (let k in series) {
            let color = colors[datasets.length];
            datasets.push({
                label: k,
                lineTension: 0,
                backgroundColor: color,
                borderColor: color,
                borderWidth: 1,
                fill: false,
                pointRadius: 0,
                data: series[k]
            })
        }

        var ctx = document.getElementById('chart'+String(this.props.index))
        this.chart = new Chart(ctx, {
            type: 'line',
            data: {
                datasets: datasets
            },
            options: {
                animation: {
                    duration: 0
                },
                hover: {
                    animationDuration: 0
                },
                responsiveAnimationDuration: 0,
                scales: {
                    xAxes: [{
                        type: "linear",
                        display: true,
                        ticks: {
                            suggestedMin: 0,
                        }
                    }],
                    yAxes: [{
                        display: true,
                    }]
                },
            }
        })
        this.chart.update();
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
                        return <pre key={index} onClick={(e) => this.props.onClick(e, index)}>{event}</pre>
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

            // Time series information
            time_series: [],

            // Current position
            history_pos: 0,

            // Step history for the current event.
            steps: [],

            // Current step position
            history_step: undefined,

            // Whether there is a file loaded.
            file_loaded: false,

            // Whether a query is in process
            querying: false
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
            this.setState({
                hcspCode: hcspCode,
                print_info: response.data.print_info,
                hcspFileName: this.fileSelector.files[0].name,
                file_loaded: true,
                history: [],
                events: [],
                time_series: [],
                history_pos: 0,
                steps: [],
                history_step: undefined
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
            time_series: response.data.time_series,
        })
    };

    nextEvent = (e) => {
        this.setState((state) => ({
            history_pos: state.history_pos + 1,
            steps: [],
            history_step: undefined,
        }))
    };

    prevEvent = (e) => {
        this.setState((state) => ({
            history_pos: state.history_pos - 1,
            steps: [],
            history_step: undefined,
        }))
    };

    eventOnClick = (e, i) => {
        this.setState({
            history_pos: i,
            steps: [],
            history_step: undefined
        })
    }

    nextStep = async (e) => {
        if (this.state.history_step !== undefined) {
            // Already exploring steps
            if (this.state.history_step === this.state.steps.length - 2) {
                // At the last step of the current event, return to exploring events
                this.setState((state) => ({
                    history_pos: state.history_pos + 1,
                    steps: [],
                    history_step: undefined,
                }));
            } else {
                // Otherwise, continue to next step in the current event
                this.setState((state) => ({
                    history_step: state.history_step + 1,
                }))
            }
        } else {
            // Not exploring steps: query the server for steps of the current
            // event
            const hpos = this.state.history_pos;
            const infos = []
            for (let i = 0; i < this.state.hcspCode.length; i++) {
                infos.push({
                    'hp': this.state.hcspCode[i],
                    'pos': this.state.history[hpos][i].pos,
                    'state': this.state.history[hpos][i].state,
                });
            }
            const data = {
                infos: infos,
                start_event: (hpos !== 0),
            }
            this.setState({querying: true})
            const response = await axios.post('/run_hcsp_steps', data);
            this.setState({querying: false})
            const history = response.data.history;
            if (history.length === 1) {
                // Directly go to the next event
                this.setState((state) => ({
                    history_pos: state.history_pos + 1,
                    steps: [],
                    history_step: undefined,
                }))
            } else {
                // Otherwise, start traversing the steps
                this.setState((state) => ({
                    steps: response.data.history,
                    history_step: 0,                    
                }))
            }    
        }
    };

    prevStep = async (e) => {
        if (this.state.history_step !== undefined) {
            // Already exploring steps
            if (this.state.history_step === 0) {
                // At the first step of the current event, return to exploring events
                this.setState({
                    steps: [],
                    history_step: undefined,
                });
            } else {
                // Otherwise, go to previous step in the current event
                this.setState((state) => ({
                    history_step: state.history_step - 1,
                }))
            }
        } else {
            // Not exploring steps: query the server for steps of the previous
            // event, then go to the last step of that event.
            const hpos = this.state.history_pos;
            const infos = []
            for (let i = 0; i < this.state.hcspCode.length; i++) {
                infos.push({
                    'hp': this.state.hcspCode[i],
                    'pos': this.state.history[hpos-1][i].pos,
                    'state': this.state.history[hpos-1][i].state,
                });
            }
            const data = {
                infos: infos,
                start_event: (hpos-1 !== 0),
            }
            const response = await axios.post('/run_hcsp_steps', data);
            const history = response.data.history;
            if (history.length === 1) {
                // Directly go to the previous event
                this.setState((state) => ({
                    history_pos: state.history_pos - 1,
                    steps: [],
                    history_step: undefined,
                }))
            } else {
                // Otherwise, traverse the steps starting at the end
                this.setState((state) => ({
                    history_pos: state.history_pos - 1,
                    steps: response.data.history,
                    history_step: response.data.history.length - 2,
                }))
            }    
        }
    };

    setStateAsync = (state) => {
        return new Promise((resolve) => {
            this.setState(state, resolve);
        });
    };

    eventLine = () => {
        if (this.state.history.length === 0) {
            return "No data"
        } else {
            const events = this.state.events;
            var res;
            if (events[events.length - 1] === 'deadlock') {
                res = String(events.length-2) + " events."
            } else {
                res = String(events.length-2) + "+ events."
            }
            res += " Current event: "
            if (this.state.history_pos === 0) {
                res += "start."
            } else if (this.state.history_pos === events.length - 1) {
                res += "end."
            } else {
                res += String(this.state.history_pos) + "."
            }
            if (this.state.history_step !== undefined) {
                res += " Current step: " + String(this.state.history_step+1) + "/" +
                       String(this.state.steps.length-1)
            }
            return res
        }
    }

    render() {
        return (
            <div>
                <Navbar bg="light" variant="light">
                    <Navbar.Brand href="#">HCSP Simulator</Navbar.Brand>
                    <Nav className="mr-auto">
                        <Button variant={"primary"} onClick={this.handleFileSelect}>Read HCSP File</Button>
                        <span style={{marginLeft:'20px',fontSize:'x-large'}}>{this.state.hcspFileName}</span>
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

                        <Button variant="secondary" title={"forward"} onClick={this.nextStep}
                            disabled={this.state.querying || this.state.history.length === 0 || this.state.history_pos === this.state.history.length-1}>
                            <FontAwesomeIcon icon={faCaretRight} size="lg"/>
                        </Button>

                        <Button variant="secondary" title={"backward"} onClick={this.prevStep}
                            disabled={this.state.querying || this.state.history.length === 0 ||
                                (this.state.history_pos === 0 && this.state.history_step === undefined)}>
                            <FontAwesomeIcon icon={faCaretLeft} size="lg"/>
                        </Button>

                        <span style={{marginLeft:'20px',fontSize:'large',marginTop:"auto",marginBottom:"auto"}}>
                            {this.eventLine()}
                        </span>
                    </ButtonToolbar>
                </div>

                <hr/>
                <Container className="left">
                    {this.state.print_info.map((info, index) => {
                        const lines = info[0];
                        const mapping = info[1];
                        if (this.state.history.length === 0) {
                            // No data is available
                            return <Process key={index} index={index} lines={lines}
                                            start={undefined} end={undefined} state={[]}
                                            time_series={undefined}/>
                        } else {
                            const hpos = this.state.history_pos;
                            const hstep = this.state.history_step;
                            var pos, state;
                            if (hstep === undefined) {
                                pos = this.state.history[hpos][index].pos;
                                state = this.state.history[hpos][index].state;    
                            } else {
                                pos = this.state.steps[hstep][index].pos;
                                state = this.state.steps[hstep][index].state;
                            }
                            var time_series = []
                            for (let i = 0; i < this.state.time_series.length; i++) {
                                time_series.push({
                                    time: this.state.time_series[i].time,
                                    state: this.state.time_series[i].states[index]
                                });
                            }
                            if (pos === 'end') {
                                // End of data set
                                return <Process key={index} index={index} lines={lines}
                                                start={undefined} end={undefined} state={state}
                                                time_series={time_series}/>
                            } else {
                                // Process out the 'w{n}' in the end if necessary
                                const sep = pos.lastIndexOf('.');
                                if (sep !== -1 && pos[sep+1] === 'w') {
                                    pos = pos.slice(0, sep)
                                }
                                // Find start and end position in the output
                                const start = mapping[pos][0];
                                const end = mapping[pos][1];
                                return <Process key={index} index={index} lines={lines}
                                                start={start} end={end} state={state}
                                                time_series={time_series}/>
                            }
                        }
                    })}
                </Container>
                <Container className="right">
                    <Events events={this.state.events} current_index={this.state.history_pos}
                            onClick={this.eventOnClick}/>
                </Container>
            </div>
        );
    }
}

export default App;
