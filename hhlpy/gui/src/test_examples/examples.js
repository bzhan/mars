export const test_examples = {
    e1: {
            pre: "x >= 0.12345",
            post: "x >= 1",
            hp: "x := x+1.23456;\nif (true) {\n  skip;\n} else {\n  y := 1; \n}\
                \n<x_dot=1 & x < 5>\n  invariant [x >= 1];"
    },
    e2: {
            pre: "x >= 1 & y == 10 & z == -2",
            post: "x >= 1 & y >= 0",
            hp: "<x_dot = y, y_dot = z + y^2 - y & y > 0> \n  invariant \n    [x >= 1];"
    },
    e3: {
            pre: "v <= V & A > 0", 
            hp: "a := A;\n <x_dot = v, v_dot = a & v < V>",
            post: "v <= V",
    },
    e4: {
            pre: "x >= 0 & y >= 0",
            hp: "{\n  x := x + 1;\n  y := y + 1;\n}*\n{\n  x := x + 1;\n} ++ {\n  y := y + 1;\n}",
            post: "x >= 0 & y >= 0"
    }
}