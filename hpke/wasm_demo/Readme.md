# WASM Demo

WASM and hacpsec doesn't play nicely together yet.

### Setup

- Comment out `evercrypt_cryptolib` in the `hpke` `Cargo.toml`.
- Uncomment the `crate-type` in the `hpke` `Cargo.toml`.
- Uncomment the code in `hpke.rs` below "WASM API".

### Building

```
wasm-pack build --target web
```

The `index.html` in this folder can be used to re-create the demo.
