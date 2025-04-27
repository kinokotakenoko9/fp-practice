# Lambda Calculus Playground: Interactive Interpreter with Reduction Strategies

[![preview](/lam.png)](https://fp-practice.vercel.app/) Explore and understand lambda calculus with this interactive web-based interpreter. Write and evaluate lambda expressions using common macros for numbers, booleans, and recursion. Observe the step-by-step reduction process with clear highlighting, making it an excellent tool for learning and experimenting with functional programming concepts.

**Key Features:**

- **Interactive Lambda Expression Editor:** Write and modify lambda calculus terms directly in your browser.
- **Macro Support:** Utilize predefined macros for natural numbers (Church numerals), booleans (TRUE, FALSE), conditional logic (COND, ISZERO), pairs (PAIR, FST, SND), arithmetic operations (ADD, SUCC, MUL, PRED), and recursion (Y, Z, T, FACT, FIB).
- **Step-by-Step Reduction Highlighting:** Visualize exactly what substitutions are happening at each reduction step.
- **Configurable Reduction Strategies:** Experiment with different evaluation strategies:
  - **Applicative Order (AO):** Evaluate arguments before applying the function.
  - **Normal Order (NO):** Evaluate the leftmost outermost redex first.
  - **Call-by-Value (CBV):** Evaluate arguments to values before function application.
  - **Call-by-Name (CBN):** Pass unevaluated arguments to functions.
- **Variable ID Display:** Option to show unique IDs for variables, helpful for understanding alpha conversion and avoiding naming conflicts.
- **Maximum Reduction Steps:** Control the maximum number of reduction steps to prevent infinite loops during evaluation (up to 10,000 steps).

**Try it out:** [https://fp-practice.vercel.app/](https://fp-practice.vercel.app/)

## Build (for local development):

```
cd fpprac
```

```
dune build ./bin/main.bc.js
```

```
sudo cp ./_build/default/bin/main.bc.js ../frontend/lib/main.bc.js
```

```
cd ../frontend
```

```
npm run dev
```
