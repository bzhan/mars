export const test_examples = {
    e1: "pre [x >= 0.12345];\nx := x+1.23456;\nif (true) {\n  skip;\n} else {\n  y := 1; \n}\
                \n<x_dot=1 & x < 5>\n  invariant [x >= 1];\npost [x >= 1];",
    e2: "pre [x >= 1] [y == 10] [z == -2];\n<x_dot = y, y_dot = z + y^2 - y & y > 0> \n  invariant \n    [x >= 1];\npost [x >= 1] [y >= 0];",
    e3: "pre [v <= V] [A > 0];\na := A;\n <x_dot = v, v_dot = a & v < V>\npost [v <= V];",
    e4: "pre [x >= 0] [y >= 0];\n{\n  x := x + 1;\n  y := y + 1;\n}* \n invariant[x >= 0] [y >= 0];\n{\n  x := x + 1;\n} ++ {\n  y := y + 1;\n}\npost [x >= 0] [y >= 0];",
}