- Building: Run `cabal build`.
- Testing: Run `cabal test`.
- Execution: Run `cabal exec regex-lookaround <regex>` and then type in the input, or run `cabal exec regex-lookaround <regex> [filepath]`.
- Benchmarking: Run `cabal bench`.

You can also run use the `+RTS -s` flag to get a more detailed summary of the runtime statistics. For example, run

```
cabal exec regex-lookaround +RTS -s --  "(a?){5000}a{5000}" a.txt 
```



To do the above, you will need `cabal`. I recommend using installing them via [GHCup](https://www.haskell.org/ghcup/).