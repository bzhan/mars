import React, {Component} from "react";
import G6 from "@antv/g6"
import Button from "react-bootstrap/Button";

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
        this.state.g.changeData(this.state.data)
    }

    changeChart = () => {
        let new_graph = this.state.data;
        new_graph.nodes.push(
            {id: "node3",
            x:400,
            y:200,
            label: "test another"}
        );
        this.setState({data: new_graph});
        this.drawGraph();
    };

    drawGraph = () => {
        console.log(this.props.hcspStates);
    };

    render() {
        return (
            <div>
                <Button variant="primary" title={"add hcsp process"} onClick={this.changeChart}>test</Button>
                <div id={"mountNode"}/>

            </div>

        )
    }
}

export default FlowChart;