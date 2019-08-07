import React, {Component} from "react";
import G6 from "@antv/g6"
import './flowChart.css'
import HTMLEncode from "./utils"

class FlowChart extends Component {


    constructor(props) {
        super(props);
        let default_graph = {
            nodes: [{
                id: 'node1',
                x: 100,
                y: 200,
                label: "测试测试测试"
            }, {
                id: 'node2',
                x: 300,
                y: 200
            }],
            edges: [{
                target: 'node2',
                source: 'node1',
            }]
        };
        this.state = {data: default_graph, g: undefined};
    }

    componentDidMount(): void {
        const graph = new G6.Graph({
            container: 'mountNode',
            width: window.innerWidth / 1.05,
            // fitView: 'autoZoom',
            height: 550,
            defaultNode: {
                labelCfg: {
                    // position: 'top',
                    style: {
                        fontSize: 15,
                        fill: '#666'
                    }
                }
            },
            defaultEdge: {
                labelCfg: {
                    refY: 10,
                    style: {
                        fontSize: 16,
                        fill: '#666'
                    }
                }
            },
            nodeStyle: {
                default: {
                    shape: "ellipse",
                    size: [60, 40]
                }
            },
            edgeStyle: {
                default: {
                    endArrow: true
                }
            },
            modes: {
                default: ['drag-canvas', {
                    type: 'tooltip',
                    formatText: function formatText(model) {
                        const code = model.info.code;
                        const state = model.info.state;
                        let result = "Code: " + code + "<br/>" +
                            "State: " + JSON.stringify(state);
                        if (model.info.reason !== undefined) {
                            const reason = model.info.reason;
                            result = "Code: " + HTMLEncode(code) + "<br/>" +
                                "State: " + JSON.stringify(state) + "<br/>" +
                                "Reason: " + JSON.stringify(reason);
                        }
                        return result
                    }
                }]
            },
        });
        graph.read(this.state.data);
        this.setState({g: graph});
    }

    componentDidUpdate(prevProps: Readonly<P>, prevState: Readonly<S>, snapshot: SS): void {
        this.convertStatesToChart();
    }

    convertStatesToChart = () => {
        const states = this.props.hcspStates;
        console.log(states);
        let graph = {
            nodes: [],
            edges: []
        };
        let graph_node_ids = {};
        let program_available = {};
        for (let process_id in states[0]) {
            graph_node_ids[process_id] = [];
            program_available[process_id] = true;
        }
        for (let i = 0; i < states.length; i++) {
            let process_no = 0;
            for (let process_id in states[i]) {
                let temp_state = states[i][process_id];
                const id = process_id + "_" + i.toString();
                const y = 100 + process_no * 150;
                const x = 100 + i * 225;
                let label = undefined;
                if (i < 1) {
                    label = "ID: " + process_id + "\n" + JSON.stringify(temp_state["state"]);
                } else {
                    label = JSON.stringify(temp_state["state"]);
                }

                let color = "white";
                if (temp_state.hasOwnProperty("reason")) {
                    if (program_available[process_id] === false) {
                        continue;
                    }
                    if (temp_state["reason"].hasOwnProperty("end")) {
                        if (states[i - 1][process_id].hasOwnProperty("reason")
                            && states[i - 1][process_id]["reason"].hasOwnProperty("end")) {
                            program_available[process_id] = false;
                            continue;
                        } else {
                            color = "red";
                        }
                    }
                }
                graph.nodes.push({
                    id: id,
                    x: x,
                    y: y,
                    label: label,
                    shape: "ellipse",
                    size: [120, 60],
                    style: {fill: color},
                    info: temp_state
                });
                process_no++;
                graph_node_ids[process_id].push(graph.nodes.length - 1);
            }
        }
        for (let process_id in graph_node_ids) {
            let node_list = graph_node_ids[process_id];
            for (let i = 0; i < node_list.length - 1; i++) {
                let source_state = graph.nodes[node_list[i]];
                let target_state = graph.nodes[node_list[i + 1]];
                const source_id = source_state.id;
                const target_id = target_state.id;
                let label = null;
                if (target_state.info.hasOwnProperty("reason")) {
                    if (target_state.info["reason"].hasOwnProperty("execute_delay")) {
                        label = "Delay: " + target_state.info["reason"]["execute_delay"];
                    } else if (target_state.info["reason"].hasOwnProperty("delay")) {
                        label = "Wait for Delay"
                    }
                }
                graph.edges.push({source: source_id, target: target_id, label: label});
            }
        }

        // connect the communication source node and target node
        for (let c = 0; c < 2; c++) {
            for (let i = 0; i < graph.nodes.length - 1; i++) {
                let j = i + 1;

                let source_state = graph.nodes[i];
                let target_state = graph.nodes[j];
                if (c === 1){
                    let temp_state = source_state;
                    source_state = target_state;
                    target_state = temp_state;
                }
                const source_id = source_state.id;
                const target_id = target_state.id;
                if (target_state.info.hasOwnProperty("reason") && source_state.info.hasOwnProperty("reason")) {
                    if (target_state.info["reason"].hasOwnProperty("comm_out") &&
                        source_state.info["reason"].hasOwnProperty("comm_in") &&
                        source_state.info["reason"]["comm_in"]["ch_name"] === target_state.info["reason"]["comm_out"]["ch_name"]) {
                        const label = "Comm channel: " + source_state.info["reason"]["comm_in"]["ch_name"] +
                            "\nvalue: " + source_state.info["reason"]["comm_in"]["value"];
                        graph.edges.push({
                            source: source_id, target: target_id, label: label,
                            labelCfg: {
                                refY: 0, refX: 0, style: {
                                    fontSize: 16,
                                    fill: '#666'
                                }
                            }
                        });
                    }
                }
            }
        }


        this.state.g.changeData(graph);
    };


    render() {
        return (
            <div id={"mountNode"}/>
        )
    }
}

export default FlowChart;