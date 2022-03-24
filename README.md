# dhall-io

An unsuccessful attempt putting IO in Dhall

## Problem

The current approach uses unsafeIO to execute IO computations in the
normalizer. However, the normalization algorithm provides no guaratees
about redundant calls to normalize. Indeed, it calls functions in
an exponential manner:

```
1121123112112341121123112112345
```

The source program was supposed to make 5 `write` calls, one per digit.

## Possible fixes

Check the normalization algorithm (doesn't seem easy). Use an `MVar` and
sequence numbers in the `World` structure, ignoring `IO/step` calls with
numbers <= what's stored in MVar.
