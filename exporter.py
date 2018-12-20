# BSD 3-Clause License
#
# Copyright (c) 2016, 2017, The University of Sydney. All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
# * Redistributions of source code must retain the above copyright notice, this
#   list of conditions and the following disclaimer.
#
# * Redistributions in binary form must reproduce the above copyright notice,
#   this list of conditions and the following disclaimer in the documentation
#   and/or other materials provided with the distribution.
#
# * Neither the name of the copyright holder nor the names of its
#   contributors may be used to endorse or promote products derived from
#   this software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
# OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

"""exporter.py: abstract classes for exporting decompiler state"""

import abc
import csv
import logging
import os

# import src.cfg as cfg
# import src.function as function
# import src.opcodes as opcodes
# import src.patterns as patterns
# import src.tac_cfg as tac_cfg


class Exporter(abc.ABC):
    generate_dl = False
    def __init__(self, source):
        """
        Args:
          source: object instance to be exported
        """
        self.source = source

    @abc.abstractmethod
    def export(self):
        """
        Exports the source object to an implementation-specific format.
        """

class CFGDotExporter(Exporter):
    """
    Generates a dot file for drawing a pretty picture of the given CFG.

    Args:
      cfg: source CFG to be exported to dot format.
    """

    def __init__(self, cfg):
        super().__init__(cfg)

    def export(self, out_filename: str = "cfg.dot"):
        """
        Export the CFG to a dot file.

        Certain blocks will have coloured outlines:
          Green: contains a RETURN operation;
          Blue: contains a STOP operation;
          Red: contains a THROW, THROWI, INVALID, or missing operation;
          Purple: contains a SELFDESTRUCT operation;
          Orange: contains a CALL, CALLCODE, or DELEGATECALL operation;
          Brown: contains a CREATE operation.

        A node with a red fill indicates that its stack size is large.

        Args:
          out_filename: path to the file where dot output should be written.
                        If the file extension is a supported image format,
                        attempt to generate an image using the `dot` program,
                        if it is in the user's `$PATH`.
        """
        import networkx as nx

        sccg = self.source

        G = sccg.nx_graph()

        # Colour-code the graph.
        returns = {hex(block.start.pc): "green" for block in sccg.cfg.basic_blocks
                   if block.end.name == 'RETURN'}
        stops = {hex(block.start.pc): "blue" for block in sccg.cfg.basic_blocks
                if block.end.name == 'STOP'}
        throws = {hex(block.start.pc): "red" for block in sccg.cfg.basic_blocks
                  if block.end.name in ('INVALID', 'THROW', 'THROWI', 'REVERT')}
        suicides = {hex(block.start.pc): "purple" for block in sccg.cfg.basic_blocks
                    if block.end.name == 'SELFDESTRUCT'}
        # creates = {hex(block.start.pc): "brown" for block in sccg.cfg.basic_blocks
        #            if any(op.opcode == opcodes.CREATE for op in block.tac_ops)}
        # calls = {hex(block.start.pc): "orange" for block in cfg.blocks
        #          if any(op.opcode.is_call() for op in block.tac_ops)}
        color_dict = {**returns, **stops, **throws, **suicides} #, **creates, **calls}
        nx.set_node_attributes(G, "color", color_dict)

        filldict = {hex(b.start.pc): "white" \
                for b in sccg.cfg.basic_blocks if b not in sccg.states}

        for scc in sccg.sccs:
            if len(scc.vertices) > 1:
                for bb in scc.vertices:
                    if bb not in filldict:
                        filldict[hex(bb.start.pc)] = "yellow"

        for block in sccg.unvisited_blocks:
            filldict[hex(block.start.pc)] = ''

        nx.set_node_attributes(G, "fillcolor", filldict)

        nx.set_node_attributes(G, "style", "filled")

        # Annotate each node with its basic block's internal data for later display
        # if rendered in html.
        nx.set_node_attributes(G, "id", {hex(block.start.pc): hex(block.start.pc)
                                         for block in sccg.cfg.basic_blocks})

        block_strings = {}
        for block in sccg.cfg.basic_blocks:

            block_string = '{}\n{}\n\n'.format(
                    str(block), str(sccg.scc_set[block]))

            block_content = ""

            if block in sccg.scc_set[block].states:
                block_content += "init state:\n{}\n".format( \
                        sccg.scc_set[block].states[block])

            block_content += "\n\n{}\n\n".format(
                    '\n'.join('{}:{}'.format(hex(ins.pc),
                        str(ins)) for ins in block.instructions))
    
            if block in sccg.states:
                block_content += "final state:\n{}\n".format(sccg.states[block])

            block_strings[hex(block.start.pc)] = block_string + block_content
        nx.set_node_attributes(G, "tooltip", block_strings)

        # Write non-dot files using pydot and Graphviz
        if "." in out_filename and not out_filename.endswith(".dot"):
            pdG = nx.nx_pydot.to_pydot(G)
            extension = out_filename.split(".")[-1]

            # If we're producing an html file, write a temporary svg to build it from
            # and then delete it.
            if extension == "html":
                html = svg_to_html(pdG.create_svg().decode("utf-8"))
                # cfg.function_extractor
                if not out_filename.endswith(".html"):
                    out_filename += ".html"
                with open(out_filename, 'w') as page:
                    logging.info("Drawing CFG image to '%s'.", out_filename)
                    page.write(html)
            else:
                pdG.set_margin(0)
                pdG.write(out_filename, format=extension)

        # Otherwise, write a regular dot file using pydot
        else:
            try:
                if out_filename == "":
                    out_filename = "cfg.html"
                nx.nx_pydot.write_dot(G, out_filename)
                logging.info("Drawing CFG image to '%s'.", out_filename)
            except:
                logging.info("Graphviz missing. Falling back to dot.")
                if out_filename == "":
                    out_filename = "cfg.dot"
                nx.nx_pydot.write_dot(G, out_filename)
                logging.info("Drawing CFG image to '%s'.", out_filename)

                          # : function.FunctionExtractor
def svg_to_html(svg: str, function_extractor = None) -> str:
    """
    Produces an interactive html page from an svg image of a CFG.

    Args:
        svg: the string of the SVG to process
        function_extractor: a FunctionExtractor object containing functions
                            to annotate the graph with.

    Returns:
        HTML string of interactive web page source for the given CFG.
    """

    lines = svg.split("\n")
    page = []

    page.append("""
              <html>
              <body>
              <style>
              .node
              {
                transition: all 0.05s ease-out;
              }
              .node:hover
              {
                stroke-width: 1.5;
                cursor:pointer
              }
              .node:hover
              ellipse
              {
                fill: #EEE;
              }
              textarea#infobox {
                position: fixed;
                display: block;
                top: 0;
                right: 0;
              }

              .dropbutton {
                padding: 10px;
                border: none;
              }
              .dropbutton:hover, .dropbutton:focus {
                background-color: #777777;
              }
              .dropdown {
                margin-right: 5px;
                position: fixed;
                top: 5px;
                right: 0px;
              }
              .dropdown-content {
                background-color: white;
                display: none;
                position: absolute;
                width: 70px;
                box-shadow: 0px 5px 10px 0px rgba(0,0,0,0.2);
                z-index: 1;
              }
              .dropdown-content a {
                color: black;
                padding: 8px 10px;
                text-decoration: none;
                font-size: 10px;
                display: block;
              }

              .dropdown-content a:hover { background-color: #f1f1f1; }

              .show { display:block; }
              </style>
              """)

    for line in lines[3:]:
        page.append(line)

    page.append("""<textarea id="infobox" disabled=true rows=40 cols=80></textarea>""")

    # Create a dropdown list of functions if there are any.
    if function_extractor is not None:
        page.append("""<div class="dropdown">
               <button onclick="showDropdown()" class="dropbutton">Functions</button>
               <div id="func-list" class="dropdown-content">""")

        for i, f in enumerate(function_extractor.functions):
            if f.is_private:
                page.append('<a id=f_{0} href="javascript:highlightFunction({0})">private #{0}</a>'.format(i))
            else:
                if f.signature:
                    page.append(
                        '<a id=f_{0} href="javascript:highlightFunction({0})">public {1}</a>'.format(i, f.signature))
                else:
                    page.append('<a id=f_{0} href="javascript:highlightFunction({0})">fallback</a>'.format(i))
        page.append("</div></div>")

    page.append("""<script>""")

    if function_extractor is not None:
        func_map = {i: [b.ident() for b in f.body]
                    for i, f in enumerate(function_extractor.functions)}
        page.append("var func_map = {};".format(func_map))
        page.append("var highlight = new Array({}).fill(0);".format(len(func_map)))

    page.append("""
               // Set info textbox contents to the title of the given element, with line endings replaced suitably.
               function setInfoContents(element){
                   document.getElementById('infobox').value = element.getAttribute('xlink:title').replace(/\\\\n/g, '\\n');
               }

               // Make all node anchor tags in the svg clickable.
               for (var el of Array.from(document.querySelectorAll(".node a"))) {
                   el.setAttribute("onclick", "setInfoContents(this);");
               }

               const svg = document.querySelector('svg')
               const NS = "http://www.w3.org/2000/svg";
               const defs = document.createElementNS( NS, "defs" );

               // IIFE add filter to svg to allow shadows to be added to nodes within it
               (function(){
                 defs.innerHTML = makeShadowFilter()
                 svg.insertBefore(defs,svg.children[0])
               })()

               function colorToID(color){
                 return color.replace(/[^a-zA-Z0-9]/g,'_')
               }

               function makeShadowFilter({color = 'black',x = 0,y = 0, blur = 3} = {}){
                 return `
                 <filter id="filter_${colorToID(color)}" x="-40%" y="-40%" width="250%" height="250%">
                   <feGaussianBlur in="SourceAlpha" stdDeviation="${blur}"/>
                   <feOffset dx="${x}" dy="${y}" result="offsetblur"/>
                   <feFlood flood-color="${color}"/>
                   <feComposite in2="offsetblur" operator="in"/>
                   <feMerge>
                     <feMergeNode/>
                     <feMergeNode in="SourceGraphic"/>
                   </feMerge>
                 </filter>
                 `
               }

               // Shadow toggle functions, with filter caching
               function addShadow(el, {color = 'black', x = 0, y = 0, blur = 3}){
                 const id = colorToID(color);
                 if(!defs.querySelector(`#filter_${id}`)){
                   const d = document.createElementNS(NS, 'div');
                   d.innerHTML = makeShadowFilter({color, x, y, blur});
                   defs.appendChild(d.children[0]);
                 }
                 el.style.filter = `url(#filter_${id})`
               }

               function removeShadow(el){
                 el.style.filter = ''
               }

               function hash(n) {
                 var str = n + "rainbows" + n + "please" + n;
                 var hash = 0;
                 for (var i = 0; i < str.length; i++) {
                   hash = (((hash << 5) - hash) + str.charCodeAt(i)) | 0;
                 }
                 return hash > 0 ? hash : -hash;
               };

               function getColor(n, sat="80%", light="50%") {
                 const hue = hash(n) % 360;
                 return `hsl(${hue}, ${sat}, ${light})`;
               }

               // Add shadows to function body nodes, and highlight functions in the dropdown list
               function highlightFunction(i) {
                 for (var n of Array.from(document.querySelectorAll(".node ellipse"))) {
                   removeShadow(n);
                 }

                 highlight[i] = !highlight[i];
                 const entry = document.querySelector(`.dropdown-content a[id='f_${i}']`)
                 if (entry.style.backgroundColor) {
                   entry.style.backgroundColor = null;
                 } else {
                   entry.style.backgroundColor = getColor(i, "60%", "90%");
                 }

                 for (var j = 0; j < highlight.length; j++) {
                   if (highlight[j]) {
                     const col = getColor(j);
                     for (var id of func_map[j]) {
                       var n = document.querySelector(`.node[id='${id}'] ellipse`);
                       addShadow(n, {color:`${col}`});
                     }
                   }
                 }
               }

               // Show the dropdown elements when it's clicked.
               function showDropdown() {
                 document.getElementById("func-list").classList.toggle("show");
               }
               window.onclick = function(event) {
                 if (!event.target.matches('.dropbutton')) {
                   var items = Array.from(document.getElementsByClassName("dropdown-content"));
                   for (var item of items) {
                     item.classList.remove('show');
                   }
                 }
               }
              </script>
              </html>
              </body>
              """)

    return "\n".join(page)
