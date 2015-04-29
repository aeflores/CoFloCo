# -*- mode: ruby -*-
# vi: set ft=ruby :

# This is a Vagrant file (https://docs.vagrantup.com/v2/).  Use this
# to get a standard development environment for the ABS tools.

# To get started, install vagrant
# (https://www.vagrantup.com/downloads.html) and VirtualBox
# (https://www.virtualbox.org/wiki/Downloads).  Then, from this
# directory, run "vagrant up".  When run the first time, this command
# will download and install an ABS environment; subsequent invocations
# will be much faster.

# To use the tools, execute "vagrant up" then "vagrant ssh".

# For running graphical programs from inside the VM (eclipse,
# key-abs), you will need an X server installed: XQuartz
# (http://xquartz.macosforge.org) for OS X or Xming
# (http://sourceforge.net/projects/xming/) for Windows.

# If you want to modify the installed software, edit the
# "config.vm.provision" at the end of this file.

# Vagrantfile API/syntax version. Don't touch unless you know what you're doing!
VAGRANTFILE_API_VERSION = "2"

Vagrant.configure(VAGRANTFILE_API_VERSION) do |config|
  # All Vagrant configuration is done here.  For a complete reference,
  # please see the online documentation at
  # https://docs.vagrantup.com/v2/

  config.vm.box = "ubuntu/trusty64"
  config.vm.post_up_message = <<-MSG
Welcome to the CoFloCo development VM.
On Windows / Mac OS X, start an X server (Xming / XQuartz)
MSG

  config.ssh.forward_x11 = true

  config.vm.provider "virtualbox" do |vb|
    vb.memory = 4096
    vb.cpus = 2
    vb.name = "CoFloCo development VM (Vagrant)"
  end

  # Install necessary software
  config.vm.provision "shell",
                      privileged: false,
                      inline: <<-SHELL
echo
echo "Installing system updates"
echo
sudo apt-get update -y -q
sudo apt-get dist-upgrade -y
echo
echo
echo "Installing prolog"
echo
sudo apt-get install -y -q swi-prolog 

if [ -z "$(grep 'export LD_LIBRARY_PATH=*' /home/vagrant/.bashrc)" ] ; then
cat >>/home/vagrant/.bashrc <<EOF
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/vagrant/src/lib/
EOF
fi

 SHELL

end
