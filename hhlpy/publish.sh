#!/bin/bash
# Publish HHLPy on the Python Package Index

cd "$(dirname "${BASH_SOURCE[0]}")"
rm -f -R ./dist/src
rm -f -R ./dist/env
rm -f -R ./dist/dist
mkdir ./dist/src
rsync -ar ../ss2hcsp ./dist/src
rsync -ar ../hhlpy ./dist/src --exclude=dist/** --exclude=dist --exclude=gui/node_modules/**

cd ./dist/src/hhlpy/gui
npm install
npm run build
cd -

cd dist
python -m venv env
source env/bin/activate
python -m pip install pip-tools
pip-compile pyproject.toml
pip-sync 
python -m pip install -e .

python -m pip install build twine
python -m build

echo "Run \`source $(dirname "${BASH_SOURCE[0]}")/dist/env/bin/activate\` and \`python3 -m hhlpy\` to test."
echo "Make sure you have not forgotten to update the version number in \`pyproject.toml\` and run \`twine upload $(dirname "${BASH_SOURCE[0]}")/dist/dist/*\` to publish."

# cd dist/
# (venv) $ unzip realpython_reader-1.0.0-py3-none-any.whl -d reader-whl
# (venv) $ tree reader-whl/