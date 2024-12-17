# Yardbird
This chicken lays `egg`s...

# Benchmark Results

[Scarecrow](https://scarecrow.sgt-pl.com/)

# Running BMC Test

`cargo run -- --filename examples/array_copy.vmt --bmc-count 0`

Currently `--bmc-count` doesn't do anything, so this will just run BMC on the input system up to a depth of 10. 

# Notes
Currently (11/22), when you run `array_copy.vmt` you will find the following instances: 

```
[
  "(= (Read-Int-Int (Write-Int-Int b i 4) i) 4)",
  "(= (Read-Int-Int (Write-Int-Int b i 4) i) (Read-Int-Int b i))",
  "(= (Read-Int-Int (Write-Int-Int b i 5) i) 5)",
  "(= (Read-Int-Int (Write-Int-Int b i 5) i) (Read-Int-Int b i))",
  "(= (Read-Int-Int (Write-Int-Int b i 3) i_next) (Read-Int-Int b i_next))",
]
```

I don't like these instances as they contain subterms that are non-variable, 4 and 5. 
For more difficult problems, these instances won't generalize as they refer directly
to a particular case, the case where 4 is written into array b for the first instance. 

To get around this we need to be smarter about how we choose substitutions in the 
conflict scheduler. I thought something like the below would work but the type 
of `new_term_without_constants` is `RecExpr<L>` and not `L`. I couldn't figure
out a way to build a term that was of type `L` directly. 

But this problem seems like something egg should deal with directly, like we have a 
node in the egraph and we want to look at all the equivalent terms and choose the 
one we like the best. I think I'm just thinking about it the wrong way. 

```rust
for node in &eclass.nodes {
  if node.to_string().contains(VARIABLE_FRAME_DELIMITER) {
    // Always return a variable if one is available.
    return node.clone();
  } else if node.children().len() > 0 {
    let new_children = |id: Id| find_best_variable_substitution(egraph, &egraph[id]);
    let new_term_without_constants = node.build_recexpr(new_children);
    println!("{:?}", egraph.lookup_expr(&dd));
    println!("new term: {}", dd);
    return new_term_without_constants;
  }
}
```

# Running all Benchmarks 
To run all of the benchmarks we currently have run:  
`cargo run -- --filename blah  --run-all > all.txt `
The filename doesn't matter. 

# Getting More Information into the EGraph

Right now (12/9) on `array_copy_increment_ind.vmt` we are unable to find any instantiations without constants. 
We could just remove the limitation on generating instantiations with no constants, but that doesn't solve the 
problem. The main problem is that we find an instantitation like: 

`(= (Read-Int-Int (Write-Int-Int b@1 i@1 7720) i@1) 7720)`

This is true, but what we really want if we look at the program is:
`(= (Read-Int-Int (Write-Int-Int b@1 i@1 (+ 1 (Read-Int-Int a@1 i@1))) i@1) (+ 1 (Read-Int-Int a@1 i@1)))`

In this case, the EGraph doesn't know about the equality 7720 = 7719 + 1. What happens is that when we're 
adding the function interpretation from the model we add `(Write b@1 i@1 7720)` and we forget the fact that
how we got to 7720 was by adding 1 to the Read term. 

We should be able to evaluate some terms in the BMC model and add some facts to the egraph that way.

;(and (= (Write-Int-Int b@0 i@0 (+ 1 (Read-Int-Int a@0 i@0))) b@1) (= (+ i@0 1) i@1) (= a@0 a@1) (= Z@0 Z@1))

terms currently added:

b@0
i@0
b@1 
a@0
a@0

don't have:
tt: Z3Object = (+ 1 (Read-Int-Int a@0 i@0))

egraph.join(model.eval(tt), tt)

# Strange Behavior with Z3VarContext
Moving Z3VarContext to before a call to `smt.to_bmc()` changes affects whether or not we terminate on `array_copy.vmt`. I have no idea why this happens. Maybe Z3VarContext changes the variable Commands in `smt`, but I printed out the bmc queries in both cases and they're exactly the same. Maybe it causes something strange to happen in the Z3 Context. Either way it might be worth digger a little more into. 

# TODOs
- [ ] remove let statements when VMTModel is built so that we don't have to call LetExtract so much
- [ ] move benchmarks to using `cargo bench`
- [ ] further testing of cost function
- [x] fix 2dim benchmark with arrays of arrays
- [x] proper error handling
- [x] computing interpolants
- [x] ranking violations that egg finds
