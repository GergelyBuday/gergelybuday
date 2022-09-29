---
layout: post
title:  "Setting up a Github Page"
date:   2022-09-20 
categories: technical 
permalink: setting-up-a-github-page
---
# Introduction

[Github Pages](https://pages.github.com/)
is a simple way of generating static websites from 
[markdown]i(https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax)
files, using the 
[Jekyll](https://jekyllrb.com/)
software.

For running a GitHub Pages blog, you need mainly these:

- setting DNS A and AAAA records for your domain name: pointing to GitHub Pages' servers
- creating a GitHub repository and registering it for GitHub Pages
- setting a TXT record to make a connection between your domain name and GitHub Pages
- installing Ruby, Bundler and Jekyll on your machine
- creating the file structure in your repository's docs directory with Jekyll
- testing your page locally
- testing your page on GitHub Pages

# Setting DNS records for your domain name

DNS is [Domain Name System](https://en.wikipedia.org/wiki/Domain_Name_System),
a method to assign IP addresses to machine names. A DNS A record sets an 
[IPv4](https://en.wikipedia.org/wiki/IPv4)
address for a domain name like formalisation.org, an AAAA record registers
an 
[IPv6](https://en.wikipedia.org/wiki/IPv6) 
address.

I suggest you to do this first, as this takes time to go through DNS servers.
For using your domain name for your blog, you need to set its A records to point to Github Pages' IPv4 addresses and AAAA records to its IPv6 addresses. The result should be this, using the dig command:

```
$ dig formalisation.org
...
;; ANSWER SECTION:
formalisation.org.      3600    IN      A       185.199.109.153
formalisation.org.      3600    IN      A       185.199.110.153
formalisation.org.      3600    IN      A       185.199.111.153
formalisation.org.      3600    IN      A       185.199.108.153
```
and
```
$ dig formalisation.org -t AAAA
...
;; ANSWER SECTION:
formalisation.org.      3600    IN      AAAA    2606:50c0:8000::153
formalisation.org.      3600    IN      AAAA    2606:50c0:8001::153
formalisation.org.      3600    IN      AAAA    2606:50c0:8002::153
formalisation.org.      3600    IN      AAAA    2606:50c0:8003::153
```
The guide for this is at [Configuring an apex domain](https://docs.github.com/en/pages/configuring-a-custom-domain-for-your-github-pages-site/managing-a-custom-domain-for-your-github-pages-site#configuring-an-apex-domain) on docs.github.com.


You need to set A and AAAA records through your domain registrar's domain administration page. You might need to delete some CNAME and other records that would be in conflict with the A and AAAA records.

# Creating a GitHub repository and registering it for GitHub Pages

The basic setup is to create a repository with your GitHub username as a name:
the two should be identical. Then, go to its Settings menu, choose Pages on the
left sidebar. Choose "Deploy from branch" as a Source, the main branch and
/docs as folder. Save these. Set your Custom domain.

For details, check [Publishing from a branch](
https://docs.github.com/en/pages/getting-started-with-github-pages/configuring-a-publishing-source-for-your-github-pages-site#publishing-from-a-branch) on docs.github.com .

# Verifying your domain name with Github Pages

You need to verify your domain with Github Pages with a custom TXT record, see [Verifying a domain for your user site](https://docs.github.com/en/pages/configuring-a-custom-domain-for-your-github-pages-site/verifying-your-custom-domain-for-github-pages#verifying-a-domain-for-your-user-site) on docs.github.com .  For checking your TXT record, modify this accordingly:

```
$ dig _github-pages-challenge-username.domain.name +nostats +nocomments +nocmd TXT
```
with adequate username and domain name. If you see the registered value of your TXT record, then you have made a connection from your Github Pages repository to your domain name -- A records did this the other way around.

# Installing Ruby, Bundler and Jekyll

Ruby is a popular programming environment for websites. Its plugins are called gems, and an uncautious installation of these can lead to Dependency Hell.

To avoid this, use [Installing Ruby On Rails on Ubuntu](https://gorails.com/setup/ubuntu/22.04) description on gorails.com, until installing Bundler.

To install Jekyll, cd into your GitHub repository's root directory, and write a short Gemfile:
```
gem 'jekyll'
```
and run
```
$ bundler install
```
This will install Jekyll into this directory.
# Creating a GitHub Pages site

Change your working directory to docs. Write a short Gemfile with
```
gem 'webrick'
```
Run
```
$ bundler install
```
to install webrick, a small webserver that enables checking the development of your website on localhost. That gives you a quick feedback, unlike pushing your content to Github Pages, which takes minutes to go through.

For setting up the file structure for your website, invoke
```
$ bundler exec jekyll new .
```
in the docs directory. To test whether it works correctly, invoke
```
$ bundler exec jekyll serve
```
It will tell you the URL to reach your new website, which is usually
```
http://localhost:4000
```

For official advice consult [Creating a GitHub Pages site with Jekyll](https://docs.github.com/en/pages/setting-up-a-github-pages-site-with-jekyll/creating-a-github-pages-site-with-jekyll) on docs.github.com . Caveat: I followed a different way in this description.

# Pushing your site to Github Pages

For this you need to push your essential files up to your Github Pages repository. Invoke
```
$ git status .
```
in the docs directory to see which files you should git add, commit and push. Jekyll installed a .gitignore that avoids adding generated HTML files: Github Pages will generate those on its server from the source files you pushed up. As said earlier, this process takes a few minutes. Now you can build your site with pages and posts, but this post was only about setting up the system.

