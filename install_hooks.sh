#/bin/bash

for hook in .hooks/*; do
    hook_name=$(basename "$hook")
    echo $hook_name
    cp "$hook" ".git/hooks/$hook_name" && chmod +x ".git/hooks/$hook_name"
done
echo "Done"
