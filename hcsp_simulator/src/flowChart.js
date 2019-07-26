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
            }, {
                id: 'node2',
                x: 300,
                y: 200
            }],
            edges: [{
                target: 'node2',
                source: 'node1',
                endArrow: true
            }]
        };
        this.state = {data: default_graph, g: undefined};
    }

    componentDidMount(): void {
        const graph = new G6.Graph({
            container: 'mountNode',
            width: 500,
            height: 500,
            nodeStyle: {
                default: {
                    fill: '#40a9ff',
                    stroke: '#096dd9',
                }
            },
            edgeStyle: {
                default: {
                    stroke: '#A3B1BF',
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
        let new_graph = {
            nodes: [{
                id: 'node1',
                x: 100,
                y: 200
            }, {
                id: 'node2',
                x: 300,
                y: 200
            }],
            edges: []
        };
        this.setState({data: new_graph});
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