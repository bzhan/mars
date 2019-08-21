def get_attribute_value(block, attribute):
    for node in block.getElementsByTagName("P"):
        if node.getAttribute("Name") == attribute:
            if node.childNodes:
                return node.childNodes[0].data
    return None


def get_children_info(block):
    children = [child for child in block.childNodes if child.nodeName == "Children"]
    if not children:
        return [], [], []

    assert len(children) == 1
    states, transitions, junctions = [], [], []
    for child in children[0].childNodes:
        if child.nodeName == "state":
            states.append(child)
        elif child.nodeName == "transition":
            transitions.append(child)
        elif child.nodeName == "junction":
            junctions.append(child)
    return states, transitions, junctions
