[![DOI](https://zenodo.org/badge/366747718.svg)](https://zenodo.org/badge/latestdoi/366747718)

# IsabelleIntervalNewtonMethod

Formalisation of the Inteval Newton Method in generic proof assistant [Isabelle/HOL](https://isabelle.in.tum.de/) as part of a bachelor's thesis in computer science at TUM (Technische Universität München).

Advisor: Dr. Manuel Eberl\
Supervisor: Prof. Tobias Nipkow\
[Chair for Logic and Verification](https://www21.in.tum.de/)

## How to Use the Implementation?

in Executable.thy with: `value "newton_floatarith eps f prec ivl"`

- eps, prec are natural numbers; recommended values are 30 or 50 for both
- f is a function in floatarith form (Approximation.thy)
- ivl is a float interval

__Result:__ float interval list option

Example:

```
definition f where "f = floatarith.Var 0"
definition I where "I = Interval''(-10,10)"
value "newton_floatarith 30 f 30 I"
	= "Some [Interval (Float 0 (- 1), Float 0 0)]"
```

## Helper Functions:

#### newton\_floatarith\_max\_its

additional argument for max iterations: `value "newton_floatarith_max_its its eps f prec ivl"`

#### newton\_floatarith\_c\_its

result is the amount of iterations until termination: `value "newton_floatarith_c_its eps f prec ivl"`

#### some\_intervals\_to\_real

converts the result to a real interval list: `some_intervals_to_real (newton ...)`

#### some\_intervals\_to\_width

converts the result to a list containing the width of the intervals: `some_intervals_to_width (newton ...)`

## Abbreviations

### Helper Functions:

- `newton_fa f ivl = some_intervals_to_real (newton_floatarith 30 f 30 ivl)`
- `newton_mi i f ivl = some_intervals_to_real (newton_floatarith_max_its i 30 f 30 ivl)`
- `newton_ci f ivl = some_intervals_to_real (newton_floatarith_c_its 30 f 30 ivl)`
- `newton_wd f ivl = some_intervals_to_width (newton_floatarith 30 f 30 ivl)`

### Floatarith:
- `f1 + f2 = floatarith.Add f1 f2`
- `f1 * f2 = floatarith.Mult f1 f2`
- `- f1 = floatarith.Minus f1`
- `floatarith_Sin x`
- `x = floatarith.Var 0`
- `pos n = floatarith.Num n`
- `neg n = pos (-n)`