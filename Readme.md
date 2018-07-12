Record
============================

This package provides a `Record` datatype for the Idris language. A record is a list of keys with a corresponding value. Thanks to the powerful type system of Idris it's possible to express a record type directly and write very general functions using it. For some inspiration check out the [Event](https://github.com/leon-vv/Event), [FerryJS](https://github.com/leon-vv/FerryJS) and [Sql](https://github.com/leon-vv/Sql) modules.

Usage
-----------------------------
Make sure to install the latest version of the Idris compiler.
```idris --install record.ipkg```
Because `record` is a reserved Idris keyword the name of the package is `record_`. To use the library in another file use:
```idris -p record_ Main.idr```

Documentation
----------------------------
```idris --mkdoc ./record.ipkg```

License
----------------------------
Mozilla Public License, v. 2.0
