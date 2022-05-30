export const test_examples = {
    e1: {
            pre: "x >= 0.12345",
            post: "x >= 1",
            hp: "x := x+1.23456;\nif true\nthen skip\nelse y := 1\nendif; \
                \n<x_dot=1 & x < 5>\ninvariant [x >= 1]"
    },
    e2: {
            pre: "x >= 1 && y == 10 && z == -2",
            post: "x >= 1 && y >= 0",
            hp: "<x_dot = y, y_dot = z + y^2 - y & y > 0> \n \
                   invariant \n \
                        [x >= 1]"
    },
    e3: {
            pre: "v <= V && A > 0", 
            hp: "a := A;\n <x_dot = v, v_dot = a & v < V>",
            post: "v <= V",
    }
}