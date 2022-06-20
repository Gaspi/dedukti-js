# In browser Dedukti

## Dependencies

```sh
git clone git@github.com:kach/nearley.git
git clone git@github.com:no-context/moo.git
npm install -g nearley
cp ./nearley/lib/nearley.js ./ressources/
cp ./moo/moo.js ./ressources/
```

## Build

```sh
make Q=
```

## Run

```sh
cd build
python3 -m http.server
```


## Refresh codejar files

Download [codejar.js](https://medv.io/codejar/codejar.js) and [linenumbers.js](https://medv.io/codejar/linenumbers.js)

Remove the `export` keywords.
