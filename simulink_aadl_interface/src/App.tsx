import './App.css';
import createEngine, {
    DiagramModel,
    DefaultNodeModel,
    DiagramEngine,
    DefaultLinkModel
} from '@projectstorm/react-diagrams';
import * as React from 'react';
import {CanvasWidget} from '@projectstorm/react-canvas-core';

import {Nav, Navbar, ButtonToolbar, Button, Container, Row, Col} from "react-bootstrap"
import axios from "axios"
import getRandomColor from "./color";

class MainCanvas extends React.Component<{ model: DiagramModel; engine: DiagramEngine }, any> {
    private reader = new FileReader();
    private fileSelector: any = null;
    private fileType: string = "simulink";

    addNodes = (port_info: any) => {
        const node_name = port_info["model_name"];
        const new_node = new DefaultNodeModel(node_name, getRandomColor());
        for (let i = 0; i < port_info["Inport"].length; i++) {
            new_node.addInPort("In name:" + port_info["Inport"][i])
        }
        for (let i = 0; i < port_info["Outport"].length; i++) {
            new_node.addOutPort("Out name:" + port_info["Outport"][i])
        }
        this.props.model.addNode(new_node);
        this.props.engine.repaintCanvas();
    };

    handleFiles = () => {
        this.reader.onloadend = async () => {
            let text = this.reader.result as string;
            let response:any = null;
            if (this.fileType === 'simulink') {
                response = await axios.post("/get_simulink_port", text);
            }else{
                response = await axios.post("/get_AADL_port", text);
            }
            let port_info = response.data;
            this.addNodes(port_info);
        };
        this.reader.readAsText(this.fileSelector.files[0]);
    };


    buildFileSelector = () => {
        const fileSelector = document.createElement('input');
        fileSelector.type = "file";
        fileSelector.onchange = this.handleFiles;
        return fileSelector;
    };

    selectSimulinkFile = (e: any) => {
        this.fileType = "simulink";
        this.fileSelector.click();
    };

    selectAADLFile = async (e: any) => {
        this.fileType = "aadl";
        this.fileSelector.click();
    };

    save = (e: any) => {
        const links = this.props.model.getLinks() as DefaultLinkModel[];
        let result: any = {};
        for (let i = 0; i < links.length; i++) {
            const link = links[i];
            const sourcePort = link.getSourcePort();
            const targetPort = link.getTargetPort();
            if (sourcePort == null || targetPort == null) {
                continue;
            }
            const sourceNode = sourcePort.getParent() as DefaultNodeModel;
            const targetNode = targetPort.getParent() as DefaultNodeModel;

            const link_id = link.getID().toString();
            result[link_id] = {
                "source": {
                    "port": sourcePort.getOptions().name,
                    "node": sourceNode.getOptions().name
                },
                "target": {
                    "port": targetNode.getOptions().name,
                    "node": targetNode.getOptions().name
                }
            }
        }
        console.log(result);

        let pom = document.createElement('a');
        pom.setAttribute('href', 'data:text/plain;charset=utf-8,' + encodeURIComponent(JSON.stringify(result)));
        pom.setAttribute('download', "");
        pom.click();
    };

    componentDidMount(): void {
        this.fileSelector = this.buildFileSelector();
    }

    render() {
        const {engine} = this.props;
        return (
            <div>
                <Navbar bg="dark" variant="dark">
                    <Navbar.Brand href="#">Simulink AADL Simulator</Navbar.Brand>
                    <Nav className="mr-auto">
                        <Button style={{marginRight: 10}} variant={"primary"} onClick={this.selectSimulinkFile}>Add
                            Simulink</Button>
                        <Button style={{marginRight: 10}} variant={"primary"} onClick={this.selectAADLFile}>Add AADL</Button>
                        <Button style={{marginRight: 10}} variant={"primary"} onClick={this.save}>Save</Button>
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

    // //3-A) create a default node
    // var node1 = new DefaultNodeModel('Node 1', 'rgb(0,192,255)');
    // node1.setPosition(100, 100);
    // let port1 = node1.addOutPort('Int Outdfdafdafadfadfadf');
    //
    //
    // //3-B) create another default node
    // var node2 = new DefaultNodeModel('Node 2', 'rgb(192,255,0)');
    // node2.setPosition(400, 100);
    // let port2 = node2.addInPort('In');
    //
    // // link the ports
    //
    // let link1 = port1.link<DefaultLinkModel>(port2);
    // link1.getOptions().testName = 'Test';
    // link1.addLabel('Hello World!');
    //
    // //4) add the models to the root graph
    // model.addAll(node1, node2, link1);

    //5) load model into engine
    engine.setModel(model);

    //6) render the diagram!
    return <MainCanvas engine={engine} model={model}/>;
};
