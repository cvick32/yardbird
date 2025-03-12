sudo apt update
cd ~
wget https://es-static.fbk.eu/people/griggio/ic3ia/ic3ia-23.05.tar.gz
tar -xvf ic3ia-23.05.tar.gz
mv ic3ia-23.05.tar.gz ic3ia
wget https://mathsat.fbk.eu/download.php?file=mathsat-5.6.11-linux-x86_64.tar.gz
tar -xvf mathsat-5.6.11-linux-x86_64.tar.gz
mv mathsat-5.6.11-linux-x86_64.tar.gz mathsat
sudo apt install g++
export CXX=g++
sudo apt install libgmp3-dev
cd ic3ia
mkdir build
cd build
cmake .. -DMATHSAT_DIR=/home/ubuntu/mathsat -DCMAKE_BUILD_TYPE=Release
make
sudo cp ic3ia /usr/bin
