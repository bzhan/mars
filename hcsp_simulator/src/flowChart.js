import React, {Component} from "react";
import G6 from "@antv/g6"

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
            width: window.innerWidth / 2,
            height: 750,
            defaultNode:{
                shape: 'rect',
                labelCfg: {
                    position: 'top',
                    style: {
                        fill: '#666'
                    }
                }
            },
            nodeStyle: {
                default: {
                    fill: '#40a9ff',
                }
            },
            edgeStyle: {
                default: {
                    endArrow: true
                }
            }
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
            const y = 200;
            const x = 100 + i * 200;
            const label = temp_state;
            graph.nodes.push({id: id, x: x, y: y, label: label})
        }
        // this.setState({data: graph});
        // this.state.g.changeData(this.state.data);
        this.state.g.changeData(graph);
    };


    render() {
        return (
                <div id={"mountNode"}/>

        )
    }
}

export default FlowChart;