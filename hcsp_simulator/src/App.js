import './App.css';

import React from "react";

import {Nav, Navbar, ButtonToolbar, Button, Container} from "react-bootstrap"
import {FontAwesomeIcon} from '@fortawesome/react-fontawesome'
import {faPlayCircle, faSync, faCaretRight, faForward, faBackward, faCaretLeft} from '@fortawesome/free-solid-svg-icons'
import {Chart} from 'chart.js'
import axios from "axios"


const verticalLinePlugin = {
    getLinePosition: function (chart, xval) {
        const left = chart.chartArea.left;
        const right = chart.chartArea.right;
        const xstart = chart.scales['x-axis-0'].start;
        const xend = chart.scales['x-axis-0'].end;
        return (xval - xstart) / (xend - xstart) * (right - left) + left;
    },

    renderVerticalLine: function (chartInstance, pointIndex) {
        const scale = chartInstance.scales['y-axis-0'];
        const context = chartInstance.chart.ctx;
  
        if (typeof(pointIndex) === 'number') {
            // render vertical line
            const lineLeftOffset = this.getLinePosition(chartInstance, pointIndex);
            context.beginPath();
            context.strokeStyle = 'black';
            context.moveTo(lineLeftOffset, scale.top);
            context.lineTo(lineLeftOffset, scale.bottom);
            context.stroke();
        } else {
            const lineLeftOffset1 = this.getLinePosition(chartInstance, pointIndex[0]);
            const lineLeftOffset2 = this.getLinePosition(chartInstance, pointIndex[1]);
            context.fillStyle = 'lightgray';
            context.fillRect(lineLeftOffset1, scale.bottom, lineLeftOffset2-lineLeftOffset1, scale.top-scale.bottom);
        }
    },
  
    beforeDatasetsDraw: function (chart, easing) {
        if (chart.config.lineAtIndex) {
            chart.config.lineAtIndex.forEach(pointIndex => this.renderVerticalLine(chart, pointIndex));
        }
    }
};

Chart.plugins.register(verticalLinePlugin);


class Process extends React.Component {
    constructor(props) {
        super(props);
        this.state = {
            show_graph: false,
        }
    }

    render() {
        return (
            <div>
            <div>Process: {this.props.name}</div>
            <div className="program-text">
                {this.props.lines.map((str, line_no) => {
                    if (this.props.pos === undefined) {
                        return <pre key={line_no}>{str}</pre>
                    }
                    const pos = this.props.pos;
                    var bg_start, bg_end;
                    if (line_no === pos.start_x) {
                        bg_start = pos.start_y;
                    } else if (line_no > pos.start_x) {
                        bg_start = 0;
                    } else {
                        bg_start = str.length;
                    }
                    if (line_no === pos.end_x) {
                        bg_end = pos.end_y;
                    } else if (line_no < pos.end_x) {
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
                {Object.keys(this.props.state).map((key, index) => {
                    return <span key={index} style={{marginLeft: "10px"}}>{key}: {this.props.state[key]}</span>
                })}
                <span>&nbsp;&nbsp;</span>
                <a href="#" onClick={this.toggleShowGraph}>{this.state.show_graph ? "Hide graph" : "Show graph"}</a>
            </pre>
            {(this.state.show_graph && this.props.time_series !== undefined) ?
                <canvas id={'chart'+String(this.props.index)} width="400" height="100"/> : null
            }
            </div>
        );
    }

    toggleShowGraph = (e) => {
        this.setState((state) => ({
            show_graph: !state.show_graph,
        }))
    }

    componentDidUpdate() {
        const ts = this.props.time_series;
        if (!this.state.show_graph || ts === undefined) {
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

        var canvas = document.getElementById('chart'+String(this.props.index));
        this.chart = new Chart(canvas, {
            type: 'line',
            data: {
                datasets: datasets
            },
            lineAtIndex: [this.props.event_time],
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
                    return (
                        <pre key={index} title={"time: " + event.time} onClick={(e) => this.props.onClick(e, index)}>
                            <span className={index === this.props.current_index?"event-list-hl":""}>
                                {event.str}
                            </span>
                        </pre>
                    )
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

            // Info about the HCSP program
            hcsp_info: [],

            // Currently computed history. Each entry represents one
            // state in the execution.
            // Each entry contains the position and state of the program
            // at each step.
            history: [],

            // Time series information
            time_series: [],

            // Current position
            history_pos: 0,

            // Whether there is a file loaded.
            file_loaded: false,

            // Error from server.
            error: undefined,

            // Whether a query is in progress.
            querying: false
        };
        this.reader = new FileReader();
        this.fileSelector = undefined;
    }

    handleFiles = () => {
        this.reader.onloadend = async () => {
            this.setState({
                querying: true
            })
            const response = await axios.post("/parse_hcsp", {
                text: this.reader.result,
            })
            if ('error' in response.data) {
                this.setState({
                    error: response.data.error,
                    hcsp_info: [],
                    hcspFileName: this.fileSelector.files[0].name,
                    file_loaded: true,
                    history: [],
                    time_series: [],
                    history_pos: 0,
                    querying: false
                })
            } else {
                this.setState({
                    error: undefined,
                    hcsp_info: response.data.hcsp_info,
                    hcspFileName: this.fileSelector.files[0].name,
                    file_loaded: true,
                    history: [],
                    time_series: [],
                    history_pos: 0,
                    querying: false
                });    
            }
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
        this.setState({
            querying: true
        })
        const response = await axios.post("/run_hcsp", {
            hcsp_info: this.state.hcsp_info,
            num_io_events: 100,
            num_steps: 400,
        })
        if ('error' in response.data) {
            this.setState({
                error: response.data.error,
                history: [],
                time_series: [],
                querying: false
            })
        } else {
            this.setState({
                error: undefined,
                history: response.data.trace,
                time_series: response.data.time_series,
                querying: false
            })
        }
    };

    nextEvent = (e) => {
        document.getElementById('right').scrollTop += 21;
        this.setState((state) => ({
            history_pos: state.history_pos + 1,
        }))
    };

    prevEvent = (e) => {
        document.getElementById('right').scrollTop -= 21;
        this.setState((state) => ({
            history_pos: state.history_pos - 1,
        }))
    };

    eventOnClick = (e, i) => {
        this.setState({
            history_pos: i,
        })
    }

    nextStep = (e) => {
        var hpos = this.state.history_pos + 1;
        while (hpos < this.state.history.length - 1 && this.state.history[hpos].type === 'step') {
            hpos += 1;
        }
        document.getElementById('right').scrollTop += (hpos - this.state.history_pos) * 21;
        this.setState({
            history_pos: hpos
        })
    };

    prevStep = (e) => {
        var hpos = this.state.history_pos - 1;
        while (hpos > 0 && this.state.history[hpos].type === 'step') {
            hpos -= 1;
        }
        document.getElementById('right').scrollTop -= (this.state.history_pos - hpos) * 21;
        this.setState({
            history_pos: hpos
        })
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
            const history = this.state.history;
            var res;
            if (history[history.length-1].type === 'deadlock') {
                res = String(history.length-1) + " events."
            } else {
                res = String(history.length-1) + "+ events."
            }
            res += " Current event: "
            if (this.state.history_pos === 0) {
                res += "start."
            } else if (this.state.history_pos === history.length - 1) {
                res += "end."
            } else {
                res += String(this.state.history_pos) + "."
            }
            return res
        }
    }

    render() {
        const left = this.state.error !== undefined ?
            <pre className="error-message">
                Error: {this.state.error}
            </pre>
        : (
            <Container className="left">
            {this.state.hcsp_info.map((info, index) => {
                const hcsp_name = info.name;
                if ('parallel' in info) {
                    return <span key={index}>Process {hcsp_name} ::= {info.parallel.join(' || ')}</span>
                }
                else if (this.state.history.length === 0) {
                    // No data is available
                    return <Process key={index} index={index} lines={info.lines}
                                    name={hcsp_name} pos={undefined} state={[]}
                                    time_series={undefined} event_time={undefined}/>
                } else {
                    const hpos = this.state.history_pos;
                    const event = this.state.history[hpos];
                    var pos = event.infos[hcsp_name].pos;
                    var state = event.infos[hcsp_name].state;
                    var event_time;
                    if (event.type !== 'delay') {
                        event_time = event.time;
                    } else {
                        event_time = [event.time, event.time + event.delay_time];
                    }
                    var time_series = this.state.time_series[hcsp_name];
                    if (pos === 'end') {
                        // End of data set
                        return <Process key={index} index={index} lines={info.lines}
                                        name={hcsp_name} pos={undefined} state={state}
                                        time_series={time_series} event_time={event_time}/>
                    } else {
                        // Process out the 'w{n}' in the end if necessary
                        const sep = pos.lastIndexOf('.');
                        if (sep !== -1 && pos[sep+1] === 'w') {
                            pos = pos.slice(0, sep)
                        }
                        return <Process key={index} index={index} lines={info.lines}
                                        name={hcsp_name} pos={info.mapping[pos]} state={state}
                                        time_series={time_series} event_time={event_time}/>
                    }
                }
            })}
            </Container>
        );
        const right = (
            <Container id="right" className="right">
                <Events events={this.state.history} current_index={this.state.history_pos}
                        onClick={this.eventOnClick}/>
            </Container>
        );
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
                        <Button variant="success" title={"run"} onClick={this.run}
                            disabled={this.state.querying || !this.state.file_loaded || this.state.error !== undefined}>
                            <FontAwesomeIcon icon={faPlayCircle} size="lg"/>
                        </Button>

                        <Button variant="secondary" title={"refresh"} onClick={this.handleFiles}
                            disabled={this.state.querying || !this.state.file_loaded}>
                            <FontAwesomeIcon icon={faSync} size="lg"/>
                        </Button>

                        <Button variant="secondary" title={"forward"} onClick={this.nextEvent}
                            disabled={this.state.querying || this.state.history.length === 0 || this.state.history_pos === this.state.history.length-1}>
                            <FontAwesomeIcon icon={faCaretRight} size="lg"/>
                        </Button>

                        <Button variant="secondary" title={"backward"} onClick={this.prevEvent}
                            disabled={this.state.querying || this.state.history.length === 0 || this.state.history_pos === 0}>
                            <FontAwesomeIcon icon={faCaretLeft} size="lg"/>
                        </Button>

                        <Button variant="secondary" title={"step forward"} onClick={this.nextStep}
                            disabled={this.state.querying || this.state.history.length === 0 || this.state.history_pos === this.state.history.length-1}>
                            <FontAwesomeIcon icon={faForward} size="lg"/>
                        </Button>

                        <Button variant="secondary" title={"step backward"} onClick={this.prevStep}
                            disabled={this.state.querying || this.state.history.length === 0 || this.state.history_pos === 0}>
                            <FontAwesomeIcon icon={faBackward} size="lg"/>
                        </Button>

                        <span style={{marginLeft:'20px',fontSize:'large',marginTop:"auto",marginBottom:"auto"}}>
                            {this.eventLine()}
                        </span>
                    </ButtonToolbar>
                </div>

                <hr/>
                {left}
                {right}
            </div>
        );
    }
}

export default App;
