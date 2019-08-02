import React, {Component} from "react";
import G6 from "@antv/g6"
import './flowChart.css'

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
            width: window.innerWidth/1.05,
            // fitView: 'autoZoom',
            height: 550,
            defaultNode:{
                labelCfg: {
                    position: 'top',
                    style: {
                        fontSize: 20,
                        fill: '#666'
                    }
                }
            },
            defaultEdge:{
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
                    shape: "circle"
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
                        if (model.info.reason !== undefined){
                            const reason = model.info.reason;
                            result = "Code: " + code + "<br/>" +
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
        let graph = {
            nodes: [],
            edges: []
        };
        for(let i = 0; i < states.length; i++) {
            let temp_state = states[i];
            const id = i.toString();
            const y = 100;
            const x = 100 + i * 200;
            const label = JSON.stringify(temp_state["state"]);
            let color = "white";
            if (temp_state.hasOwnProperty("reason") ) {
                if (temp_state["reason"].hasOwnProperty("end")){
                    if (states[i-1].hasOwnProperty("reason") && states[i - 1]["reason"].hasOwnProperty("end")){
                        continue;
                    }else{
                        color = "red";
                    }
                }else if (temp_state["reason"].hasOwnProperty("delay")) {
                    color = "yellow";
                }
            }
            graph.nodes.push({id: id, x: x, y: y, label: label, style: {fill: color}, info: temp_state})
        }
        for(let i = 0; i < graph.nodes.length - 1; i++) {
            let source_state = graph.nodes[i];
            let target_state = graph.nodes[i + 1];
            const source_id = source_state.id;
            const target_id = target_state.id;
            let label = null;
            if (target_state.info.hasOwnProperty("reason")){
                if (target_state.info["reason"].hasOwnProperty("process_delay")){
                    label = "Delay: " + target_state.info["reason"]["process_delay"];
                }else if (target_state.info["reason"].hasOwnProperty("delay")){
                    label = "Wait for Delay"
                }
            }
            graph.edges.push({source: source_id, target: target_id, label: label});
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