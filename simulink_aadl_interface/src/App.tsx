import './App.css';
import createEngine, { DiagramModel, DefaultNodeModel, DiagramEngine, DefaultLinkModel } from '@projectstorm/react-diagrams';
import * as _ from "lodash";
import * as React from 'react';
import { CanvasWidget } from '@projectstorm/react-canvas-core';

import {Nav, Navbar, ButtonToolbar, Button, Container} from "react-bootstrap"
import {FontAwesomeIcon} from '@fortawesome/react-fontawesome'
import axios from "axios"

class MainCanvas extends React.Component<{ model: DiagramModel; engine: DiagramEngine }, any> {
    addPorts = () => {
        const nodes: DefaultNodeModel[] = _.values(this.props.model.getNodes()) as DefaultNodeModel[];
        for (let node of nodes) {
            if (node.getOptions().name === 'Node 2') {
                node.addInPort(`in-${node.getInPorts().length + 1}`, false);
            } else {
                node.addOutPort(`out-${node.getOutPorts().length + 1}`, false);
            }
        }
        this.props.engine.repaintCanvas();
    };

    addNodes = () => {
        const new_node = new DefaultNodeModel("new node", 'rgb(0,192,255)');
        new_node.addInPort("in");
        new_node.addOutPort("out");
        this.props.model.addNode(new_node);
        this.props.engine.repaintCanvas();
    };

    render() {
        const { engine } = this.props;
        return (
            <div>
                <Navbar bg="light" variant="light">
                    <Navbar.Brand href="#">Simulink AADL Simulator</Navbar.Brand>
                    <Nav className="mr-auto">
                        <Button variant={"primary"} onClick={this.addNodes}>Add Nodes</Button>
                        {}
                    </Nav>

                    <Nav>
                        <Nav.Link href="#features">Readme</Nav.Link>
                        <Nav.Link href="#deets">Contact</Nav.Link>
                    </Nav>
                </Navbar>
                <CanvasWidget className="srd-diagram" engine={engine}/>
            </div>

        );
    }
}

export default () => {
    //1) setup the diagram engine
    var engine = createEngine();

    //2) setup the diagram model
    var model = new DiagramModel();

    //3-A) create a default node
    var node1 = new DefaultNodeModel('Node 1', 'rgb(0,192,255)');
    node1.setPosition(100, 100);
    let port1 = node1.addOutPort('Int Outdfdafdafadfadfadf');

    //3-B) create another default node
    var node2 = new DefaultNodeModel('Node 2', 'rgb(192,255,0)');
    node2.setPosition(400, 100);
    let port2 = node2.addInPort('In');

    // link the ports

    let link1 = port1.link<DefaultLinkModel>(port2);
    link1.getOptions().testName = 'Test';
    link1.addLabel('Hello World!');

    //4) add the models to the root graph
    model.addAll(node1, node2, link1);

    //5) load model into engine
    engine.setModel(model);

    //6) render the diagram!
    return <MainCanvas engine={engine} model={model}/>;
};
