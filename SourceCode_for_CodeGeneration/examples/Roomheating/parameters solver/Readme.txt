1. Run compute_parameters.m to get the range of epsilon, L and maxi and max_f;
2. Simulate roomheating.mdl for bounded time;
3. Run compute_h.m to get the upper bound of the step size h (the settings of the values of parameters are based on the results computed in step 1 and the simulation results in step 2);
4. Choose reasonable values of epsilon, h, var_epsilon and T using for code generation (e.g., T=5, delta=0, epsilon=0.12, h=0.0002, var_epsilon=0.1).
