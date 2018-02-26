#!/bin/bash

stack exec -- liquid -i src src/Models.hs
stack exec -- liquid -i src src/BinahLib.hs --no-totality
stack exec -- liquid -i src src/Lib.hs
